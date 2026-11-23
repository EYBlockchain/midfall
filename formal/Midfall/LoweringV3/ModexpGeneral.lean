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
    {st st' : EvmState} {o : Outcome} {x y : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.letDecl [x] (some (Expr.builtin EVM.Op.mload [Expr.var y]))) V' st' o) :
    ∃ p v, VEnv.get V y = some p ∧ v = loadWord st.memory p.toNat ∧
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
      exec_let_mload_var_inv (x := "all_inv") (y := "gp_mptr") h1
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


variable {c : ExternalCalls} {g : ExternalGas}

structure RestSucc (p a : Nat) (v : Nat) (x : U256) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop where
  hok : o = .normal
  hret : VEnv.get V' "ret" = some 1
  hpf : VEnv.get V' "precompile_failed" = some 0
  hall : VEnv.get V' "all_inv" = some (BitVec.ofNat 256 v)
  hfirst : VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a)
  hsecond : VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 a + 32)
  hgp_mptr : VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 p - 32)
  hmptr_start : VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a)
  hr : VEnv.get V' "r" = some (BitVec.ofNat 256 blsR)
  hgp : VEnv.get V' "gp" = some x
  hstate : st' = touchMemory st (BitVec.ofNat 256 p).toNat 32

structure RestFail (st : EvmState) (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState)
    (o : Outcome) : Prop where
  hok : o = .leave
  hret : VEnv.get V' "ret" = some 0
  hpf : VEnv.get V' "precompile_failed" = some 1
  hstate : st' = st

abbrev rest4 : Block EVM.Op :=
  [ GenAst.yset "ret" (GenAst.yop EVM.Op.and
      [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
        [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]]),
    GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]),
    GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]) [Stmt.leave],
    GenAst.ylet "all_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "gp_mptr"]),
    GenAst.ylet "first_mptr" (GenAst.yvar "mptr_start"),
    GenAst.ylet "second_mptr" (GenAst.yop EVM.Op.add
      [GenAst.yvar "first_mptr", GenAst.ylit 32]),
    GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.sub
      [GenAst.yvar "gp_mptr", GenAst.ylit 32]) ]

structure RestPre (M : Nat → UInt8) (p a : Nat) (v : Nat) (x : U256)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop where
  hret : VEnv.get V "ret" = some 1
  hlen : st.returndata.length = 32
  hgp_mptr : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p)
  hmstart : VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a)
  hr : VEnv.get V "r" = some (BitVec.ofNat 256 blsR)
  hgp : VEnv.get V "gp" = some x
  hpf_some : (VEnv.get V "precompile_failed").isSome = true
  hmem : st.memory = M
  hload : loadWord M p = BitVec.ofNat 256 v

structure RestFailPre (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop where
  hret : VEnv.get V "ret" = some 0
  hpf_some : (VEnv.get V "precompile_failed").isSome = true

theorem rest_success (funs : FunEnv (Bridge.Dialect c g))
    (M : Nat → UInt8) (p a : Nat) (v : Nat) (x : U256) (hp : p < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs rest4
      (fun V st => RestPre (c := c) (g := g) M p a v x V st)
      (fun _ st V' st' o => RestSucc (c := c) (g := g) p a v x st V' st' o) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hret, hlen, hgp_mptr, hmstart, hr, hgp, hpf_some, hmem, hload⟩ := hpre
  obtain ⟨pfv, hpfv⟩ := Option.isSome_iff_exists.mp hpf_some
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
  · have h2c := ret_and_eq32_stmt (c := c) (g := g) funs (V := V) (st := st)
      ⟨(1 : U256), hret, Or.inr ⟨rfl, hlen⟩⟩ V2 st2 .normal h2
    obtain ⟨-, rv2, hret', hV2, hst2⟩ := h2c
    have hrv2 : rv2 = (1 : U256) := by
      rw [hret] at hret'
      exact (Option.some.inj hret').symm
    subst hrv2
    have hretV2 : VEnv.get V2 "ret" = some (1 : U256) := by
      rw [hV2]
      exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hret
    have hretV2set : VEnv.get (VEnv.set V "ret" (1 : U256)) "ret" = some (1 : U256) :=
      Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hret
    have hpfV2 : VEnv.get (VEnv.set V "ret" (1 : U256)) "precompile_failed" = some pfv := by
      rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
        (x := "ret") (y := "precompile_failed") (by decide)]
      exact hpfv
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
      ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
    · have h3c := exec_assign_iszero_one (c := c) (g := g) (V := V2) (st := st2) hretV2 h3
      obtain ⟨-, hV3, hst3⟩ := h3c
      have hretV3 : VEnv.get V3 "ret" = some (1 : U256) := by
        rw [hV3]
        exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
          (x := "precompile_failed") (y := "ret") (by decide)).trans hretV2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
        ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
      · have h4c := exec_guard_inv (c := c) (g := g) (rv := 1) hretV3 h4
        obtain ⟨ho4, hV4, hst4⟩ := h4c.1 rfl
        have hgpV4 : VEnv.get V4 "gp_mptr" = some (BitVec.ofNat 256 p) := by
          rw [hV4, hV3, hV2]
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "precompile_failed") (y := "gp_mptr") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "ret") (y := "gp_mptr") (by decide)]
          exact hgp_mptr
        have hmstartV4 : VEnv.get V4 "mptr_start" = some (BitVec.ofNat 256 a) := by
          rw [hV4, hV3, hV2]
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "precompile_failed") (y := "mptr_start") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "ret") (y := "mptr_start") (by decide)]
          exact hmstart
        have hst4mem : st4.memory = M := by rw [hst4, hst3, hst2]; exact hmem
        have h5c := bi_staticcall_tail_lets (c := c) (g := g) (funs := funs)
          (M := M) (p := p) (a := a) (v := v) hp
          V4 st4 ⟨hgpV4, hmstartV4, hst4mem, hload⟩ V' st' o hrest4
        obtain ⟨ho_tail, hall, hfirst, hsecond, hgpm, hmstart', hst', hV'⟩ := h5c
        refine ⟨ho_tail, ?_, ?_, hall, hfirst, hsecond, hgpm, hmstart', ?_, ?_, ?_⟩
        · -- ret
          rw [hV']
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "gp_mptr") (y := "ret") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "second_mptr") (y := "ret") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "first_mptr") (y := "ret") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "all_inv") (y := "ret") (by decide)]
          rw [hV4, hV3, hV2]
          exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
            (x := "precompile_failed") (y := "ret") (by decide)).trans hretV2set
        · -- pf
          rw [hV']
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "gp_mptr") (y := "precompile_failed") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "second_mptr") (y := "precompile_failed") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "first_mptr") (y := "precompile_failed") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "all_inv") (y := "precompile_failed") (by decide)]
          rw [hV4, hV3, hV2]
          simpa [b2w] using Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hpfV2
        · -- r
          rw [hV']
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "gp_mptr") (y := "r") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "second_mptr") (y := "r") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "first_mptr") (y := "r") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "all_inv") (y := "r") (by decide)]
          rw [hV4, hV3, hV2]
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "precompile_failed") (y := "r") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "ret") (y := "r") (by decide)]
          exact hr
        · -- gp
          rw [hV']
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "gp_mptr") (y := "gp") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "second_mptr") (y := "gp") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "first_mptr") (y := "gp") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "all_inv") (y := "gp") (by decide)]
          rw [hV4, hV3, hV2]
          rw [Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "precompile_failed") (y := "gp") (by decide),
              Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
                (x := "ret") (y := "gp") (by decide)]
          exact hgp
        · -- state
          rw [hst', hst4, hst3, hst2]
      · obtain ⟨ho4, -, -⟩ := (exec_guard_inv (c := c) (g := g) (rv := 1) hretV3 h4).1 rfl
        exact absurd ho4 hne4
    · cases h3 with
      | assignVal he hl => exact absurd rfl hne3
      | assignHalt he => exact (eval_iszero_ret_no_halt he).elim
  · cases h2 with
    | assignVal he hl => exact absurd rfl hne2
    | assignHalt he => exact (eval_ret_and_eq32_no_halt he).elim

theorem rest_failure (funs : FunEnv (Bridge.Dialect c g)) :
    StmtsContractAll (D := Bridge.Dialect c g) funs rest4
      (fun V st => RestFailPre (c := c) (g := g) V st)
      (fun _ st V' st' o => RestFail (c := c) (g := g) st V' st' o) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hret, hpf_some⟩ := hpre
  obtain ⟨pfv, hpfv⟩ := Option.isSome_iff_exists.mp hpf_some
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
  · have h2c := ret_and_eq32_stmt (c := c) (g := g) funs (V := V) (st := st)
      ⟨(0 : U256), hret, Or.inl rfl⟩ V2 st2 .normal h2
    obtain ⟨-, rv2, hret', hV2, hst2⟩ := h2c
    have hrv2 : rv2 = (0 : U256) := by
      rw [hret] at hret'
      exact (Option.some.inj hret').symm
    subst hrv2
    have hretV2 : VEnv.get V2 "ret" = some (0 : U256) := by
      rw [hV2]
      exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hret
    have hpfV2 : VEnv.get V2 "precompile_failed" = some pfv := by
      rw [hV2]
      exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
        (x := "ret") (y := "precompile_failed") (by decide)).trans hpfv
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
      ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
    · have h3c := exec_assign_iszero_zero (c := c) (g := g) (V := V2) (st := st2) hretV2 h3
      obtain ⟨-, hV3, hst3⟩ := h3c
      have hretV3 : VEnv.get V3 "ret" = some (0 : U256) := by
        rw [hV3]
        exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
          (x := "precompile_failed") (y := "ret") (by decide)).trans hretV2
      have hpfV3 : VEnv.get V3 "precompile_failed" = some 1 := by
        rw [hV3]
        exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hpfV2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
        ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
      · obtain ⟨ho4, -, -⟩ := (exec_guard_inv (c := c) (g := g) (rv := 0) hretV3 h4).2 rfl
        exact absurd ho4 (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)
      · -- the guard leaves; the tail never runs
        obtain ⟨ho, hV4, hst4⟩ := (exec_guard_inv (c := c) (g := g) (rv := 0) hretV3 h4).2 rfl
        refine ⟨ho, ?_, ?_, ?_⟩
        · rw [hV4]
          exact hretV3
        · rw [hV4]
          exact hpfV3
        · rw [hst4, hst3, hst2]
    · cases h3 with
      | assignVal he hl => exact absurd rfl hne3
      | assignHalt he => exact (eval_iszero_ret_no_halt he).elim
  · cases h2 with
    | assignVal he hl => exact absurd rfl hne2
    | assignHalt he => exact (eval_ret_and_eq32_no_halt he).elim

theorem rest_success_run (funs : FunEnv (Bridge.Dialect c g))
    (M : Nat → UInt8) (p a : Nat) (v : Nat) (x : U256) (hp : p < 2 ^ 256)
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpre : RestPre (c := c) (g := g) M p a v x V st)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (h : ExecStmts (D := Bridge.Dialect c g) funs V st rest4 V' st' o) :
    RestSucc (c := c) (g := g) p a v x st V' st' o :=
  rest_success (c := c) (g := g) funs M p a v x hp V st hpre V' st' o h

theorem rest_failure_run (funs : FunEnv (Bridge.Dialect c g))
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState)
    (hpre : RestFailPre (c := c) (g := g) V st)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (h : ExecStmts (D := Bridge.Dialect c g) funs V st rest4 V' st' o) :
    RestFail (c := c) (g := g) st V' st' o :=
  rest_failure (c := c) (g := g) funs V st hpre V' st' o h



structure WalkSucc (mem : Nat → UInt8) (p a : Nat) (x : U256) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop where
  hok : o = .normal
  hret : VEnv.get V' "ret" = some 1
  hpf : VEnv.get V' "precompile_failed" = some 0
  hall : VEnv.get V' "all_inv" =
    some (BitVec.ofNat 256 ((x.toNat : ZMod blsR)⁻¹).val)
  hfirst : VEnv.get V' "first_mptr" = some (BitVec.ofNat 256 a)
  hsecond : VEnv.get V' "second_mptr" = some (BitVec.ofNat 256 (a + 32))
  hgp_mptr : VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 (p - 32))
  hmptr_start : VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a)
  hr : VEnv.get V' "r" = some (BitVec.ofNat 256 blsR)
  hgp : VEnv.get V' "gp" = some x
  henv : st'.env = st.env
  hhalt : st'.halted = st.halted
  hmem : st'.memory = copyReturn (mxMem mem p x) p 32
    (bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32).data.toList

structure WalkFail (mem : Nat → UInt8) (p a : Nat) (x : U256) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop where
  hok : o = .leave
  hret : VEnv.get V' "ret" = some 0
  hpf : VEnv.get V' "precompile_failed" = some 1
  henv : st'.env = st.env
  hhalt : st'.halted = st.halted
  hmem : ∃ rd, st'.memory = copyReturn (mxMem mem p x) p 32 rd

def WalkPost (mem : Nat → UInt8) (p a : Nat) (x : U256) (st : EvmState)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome) : Prop :=
  WalkSucc mem p a x st V' st' o ∨ WalkFail mem p a x st V' st' o

theorem walk_success_build (mem : Nat → UInt8) (p a : Nat) (x : U256) (hp : p < 2 ^ 256) (hp32 : 32 ≤ p) (ha : a + 32 < 2 ^ 256)
    (st st1 st' : EvmState) (resp : CallResponse)
    (V' : VEnv (Bridge.Dialect c g))
    (hst1 : st1 = finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
      (BitVec.ofNat 256 p).toNat 32)
    (hrd : resp.returndata = (bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32).data.toList)
    (hmem : st.memory = mxMem mem p x)
    (hrest : RestSucc (c := c) (g := g) p a ((x.toNat : ZMod blsR)⁻¹).val x st1 V' st' .normal) :
    WalkSucc (c := c) (g := g) mem p a x st V' st' .normal := by
  refine ⟨hrest.hok, hrest.hret, hrest.hpf, hrest.hall, hrest.hfirst, ?_,
    ?_, hrest.hmptr_start, hrest.hr, hrest.hgp, ?_, ?_, ?_⟩
  · rw [hrest.hsecond]
    change some (BitVec.ofNat 256 a + BitVec.ofNat 256 32) = some (BitVec.ofNat 256 (a + 32))
    exact congrArg some (ofNat_add_32 a ha)
  · rw [hrest.hgp_mptr]
    change some (BitVec.ofNat 256 p - BitVec.ofNat 256 32) = some (BitVec.ofNat 256 (p - 32))
    exact congrArg some (ofNat_sub_32 p hp hp32)
  · rw [hrest.hstate, show (touchMemory st1 (BitVec.ofNat 256 p).toNat 32).env = st1.env from rfl,
      hst1, finishCall_staticcall_env]
  · rw [hrest.hstate, show (touchMemory st1 (BitVec.ofNat 256 p).toNat 32).halted = st1.halted from rfl,
      hst1, Midfall.Yul.Bridge.finishCall_staticcall_halted]
  · rw [hrest.hstate, show (touchMemory st1 (BitVec.ofNat 256 p).toNat 32).memory = st1.memory from rfl,
      hst1, finishCall_staticcall_memory]
    rw [show (BitVec.ofNat 256 p).toNat = p from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]]
    rw [hrd, hmem]
theorem walk_failure_build (mem : Nat → UInt8) (p a : Nat) (x : U256) (hp : p < 2 ^ 256)
    (st st1 st' : EvmState) (resp : CallResponse)
    (V' : VEnv (Bridge.Dialect c g))
    (hst1 : st1 = finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
      (BitVec.ofNat 256 p).toNat 32)
    (hmem : st.memory = mxMem mem p x)
    (hrest : RestFail (c := c) (g := g) st1 V' st' .leave) :
    WalkFail (c := c) (g := g) mem p a x st V' st' .leave := by
  refine ⟨hrest.hok, hrest.hret, hrest.hpf, ?_, ?_, ?_⟩
  · rw [hrest.hstate, hst1, finishCall_staticcall_env]
  · rw [hrest.hstate, hst1, Midfall.Yul.Bridge.finishCall_staticcall_halted]
  · refine ⟨resp.returndata, ?_⟩
    rw [hrest.hstate, hst1, finishCall_staticcall_memory]
    rw [show (BitVec.ofNat 256 p).toNat = p from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]]
    rw [hmem]




theorem head_ret {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (hrv0 : ∃ rv, VEnv.get V "ret" = some rv) :
    VEnv.get V1 "ret" = some (1 : U256) := by
  obtain ⟨rv, hrv⟩ := hrv0
  rw [hV1, hflag]
  exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hrv

theorem head_gp_mptr {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    {p : Nat} (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (h : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p)) :
    VEnv.get V1 "gp_mptr" = some (BitVec.ofNat 256 p) := by
  rw [hV1, hflag]
  exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
    (x := "ret") (y := "gp_mptr") (by decide)).trans h

theorem head_mptr_start {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    {a : Nat} (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (h : VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a)) :
    VEnv.get V1 "mptr_start" = some (BitVec.ofNat 256 a) := by
  rw [hV1, hflag]
  exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
    (x := "ret") (y := "mptr_start") (by decide)).trans h

theorem head_r {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (h : VEnv.get V "r" = some (BitVec.ofNat 256 blsR)) :
    VEnv.get V1 "r" = some (BitVec.ofNat 256 blsR) := by
  rw [hV1, hflag]
  exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
    (x := "ret") (y := "r") (by decide)).trans h

theorem head_gp {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    {x : U256} (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (h : VEnv.get V "gp" = some x) :
    VEnv.get V1 "gp" = some x := by
  rw [hV1, hflag]
  exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
    (x := "ret") (y := "gp") (by decide)).trans h

theorem head_pf_some {V V1 : VEnv (Bridge.Dialect c g)} {resp : CallResponse}
    {w : U256} (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = w)
    (h : (VEnv.get V "precompile_failed").isSome = true) :
    (VEnv.get V1 "precompile_failed").isSome = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  have hv1 : VEnv.get V1 "precompile_failed" = some v := by
    rw [hV1, hflag]
    exact (Midfall.LoweringV3.PcsRows.venv_get_set_ne (D := Bridge.Dialect c g)
      (x := "ret") (y := "precompile_failed") (by decide)).trans hv
  rw [hv1]; rfl




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


theorem walk_success_rest (funs : FunEnv (Bridge.Dialect c g))
    (M : Nat → UInt8) (p a : Nat) (x : U256) (hp : p < 2 ^ 256)
    (V V1 : VEnv (Bridge.Dialect c g)) (st st1 : EvmState) (resp : CallResponse)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 1)
    (hst1 : st1 = finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
      (BitVec.ofNat 256 p).toNat 32)
    (hgp_mptr : VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p))
    (hgp : VEnv.get V "gp" = some x)
    (hmstart : VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a))
    (hr : VEnv.get V "r" = some (BitVec.ofNat 256 blsR))
    (hpf_some : (VEnv.get V "precompile_failed").isSome = true)
    (hrv0 : ∃ rv0, VEnv.get V "ret" = some rv0)
    (hrd : resp.returndata = (bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32).data.toList)
    (hlen1 : st1.returndata.length = 32)
    (hst1mem : st1.memory = M)
    (hload : loadWord M p = BitVec.ofNat 256 ((x.toNat : ZMod blsR)⁻¹).val)
    (hrec : ExecStmts (D := Bridge.Dialect c g) funs V1 st1 rest4 V' st' o) :
    RestSucc (c := c) (g := g) p a ((x.toNat : ZMod blsR)⁻¹).val x st1 V' st' o :=
  rest_success_run (c := c) (g := g) funs M p a ((x.toNat : ZMod blsR)⁻¹).val x hp
    V1 st1 (RestPre.mk (head_ret hV1 hflag hrv0) hlen1 (head_gp_mptr hV1 hflag hgp_mptr)
      (head_mptr_start hV1 hflag hmstart) (head_r hV1 hflag hr) (head_gp hV1 hflag hgp)
      (head_pf_some hV1 hflag hpf_some) hst1mem hload)
    V' st' o hrec

theorem walk_failure_rest (funs : FunEnv (Bridge.Dialect c g)) (p : Nat)
    (V V1 : VEnv (Bridge.Dialect c g)) (st st1 : EvmState) (resp : CallResponse)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) (o : Outcome)
    (hV1 : V1 = VEnv.set V "ret" resp.flag) (hflag : resp.flag = 0)
    (hst1 : st1 = finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
      (BitVec.ofNat 256 p).toNat 32)
    (hpf_some : (VEnv.get V "precompile_failed").isSome = true)
    (hrv0 : ∃ rv0, VEnv.get V "ret" = some rv0)
    (hrec : ExecStmts (D := Bridge.Dialect c g) funs V1 st1 rest4 V' st' o) :
    RestFail (c := c) (g := g) st1 V' st' o := by
  obtain ⟨rv0, hrv0⟩ := hrv0
  have hretV1 : VEnv.get V1 "ret" = some (0 : U256) := by
    rw [hV1, hflag]
    exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect c g) hrv0
  exact rest_failure_run (c := c) (g := g) funs V1 st1
    (RestFailPre.mk hretV1 (head_pf_some hV1 hflag hpf_some)) V' st' o hrec


theorem bi_staticcall_walk (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (gas : Nat) (hgas : consts.lookup "MODEXP_GAS" = some gas)
    (mem : Nat → UInt8) (p a : Nat) (x : U256)
    (hp : p < 2 ^ 256) (hp32 : 32 ≤ p) (ha : a + 32 < 2 ^ 256)
    (hx0 : 0 < x.toNat) (hxr : x.toNat < blsR) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (seg (helperBody consts GenAst.emitBatchInvertAt) 21 8)
      (fun V st =>
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V "gp" = some x ∧
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 blsR) ∧
        (VEnv.get V "ret").isSome ∧ (VEnv.get V "precompile_failed").isSome ∧
        st.memory = mxMem mem p x)
      (fun V st V' st' o => WalkPost mem p a x st V' st' o) := by
  rw [bi_staticcall_segment_form, hgas]
  intro V st hpre V' st' o hrun
  obtain ⟨hgp_mptr, hgp, hmstart, hr, hret_some, hpf_some, hmem⟩ := hpre
  have hout := mxMem_modexpOutput mem p x hx0 hxr
  have hvalid := modexpValidInput_of_output_some hout
  change ExecStmts (D := Bridge.Dialect (permissive (callsOf product)) g) funs V st
    [GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
        [Expr.lit (Literal.number gas), GenAst.ylit 5, GenAst.yvar "gp_mptr",
          GenAst.ylit 192, GenAst.yvar "gp_mptr", GenAst.ylit 32]),
     GenAst.yset "ret" (GenAst.yop EVM.Op.and
        [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
          [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]]),
     GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]),
     GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]) [Stmt.leave],
     GenAst.ylet "all_inv" (GenAst.yop EVM.Op.mload [GenAst.yvar "gp_mptr"]),
     GenAst.ylet "first_mptr" (GenAst.yvar "mptr_start"),
     GenAst.ylet "second_mptr" (GenAst.yop EVM.Op.add
        [GenAst.yvar "first_mptr", GenAst.ylit 32]),
     GenAst.yset "gp_mptr" (GenAst.yop EVM.Op.sub
        [GenAst.yvar "gp_mptr", GenAst.ylit 32])] V' st' o at hrun
  obtain ⟨rv0, hrv0⟩ := Option.isSome_iff_exists.mp hret_some
  have hp_toNat : (BitVec.ofNat 256 p).toNat = p := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨resp, -, hcall, hV1, hst1⟩ := exec_assign_staticcall_inv (funs := funs)
      (gas := gas) (vp := BitVec.ofNat 256 p) hgp_mptr h1
    by_cases hsucc : resp.success = true
    · -- SUCCESS
      have hflag : resp.flag = 1 := by simp [CallResponse.flag, hsucc]
      have h192 : (BitVec.ofNat 256 192).toNat = 192 := rfl
      have hinput : ByteArray.mk (readBytes st.memory (BitVec.ofNat 256 p).toNat
            (BitVec.ofNat 256 192).toNat).toArray =
          ByteArray.mk (readBytes (mxMem mem p x) p 192).toArray := by
        rw [hp_toNat, h192, hmem]
      have hcalls : (callsOf product).Call
          { kind := .staticcall, gas := BitVec.ofNat 256 gas, target := BitVec.ofNat 256 5,
            value := 0, input := readBytes st.memory (BitVec.ofNat 256 p).toNat
              (BitVec.ofNat 256 192).toNat } st resp := hcall.2 hsucc
      have hrd : resp.returndata =
          (bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32).data.toList := by
        refine callsOf_modexp_returndata
          (product := product) (req := _) (st := st) (resp := resp)
          (out := bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32) rfl ?_ ?_ hcalls hsucc
        · rw [hinput]; exact hvalid
        · rw [hinput]; exact hout
      have hlen : (bytesNatBE ((x.toNat : ZMod blsR)⁻¹).val 32).data.toList.length = 32 := by
        rw [Array.length_toList, ByteArray.size_data]
        exact Midfall.Assumptions.bytesNatBE_size _ 32
      have hlen1 : st1.returndata.length = 32 := by
        rw [hst1]; show resp.returndata.length = 32; rw [hrd]; exact hlen
      have hst1mem : st1.memory = (finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
          (BitVec.ofNat 256 p).toNat 32).memory := by rw [hst1]
      have hload : loadWord (finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
            (BitVec.ofNat 256 p).toNat 32).memory p =
          BitVec.ofNat 256 ((x.toNat : ZMod blsR)⁻¹).val := by
        rw [finishCall_staticcall_memory]
        rw [hp_toNat, hrd, hmem]
        exact loadWord_copyReturn_bytesNatBE (mem := mxMem mem p x) (p := p)
          (v := ((x.toNat : ZMod blsR)⁻¹).val) (zmod_inv_val_lt x)
      have hrest := walk_success_rest (c := permissive (callsOf product)) (g := g) funs
        ((finishCall .staticcall st resp (BitVec.ofNat 256 p).toNat 192
          (BitVec.ofNat 256 p).toNat 32).memory) p a x hp
        V V1 st st1 resp V' st' o hV1 hflag hst1 hgp_mptr hgp hmstart hr hpf_some
        ⟨rv0, hrv0⟩ hrd hlen1 hst1mem hload hrest1
      have hok := hrest.hok
      rw [hok] at ⊢
      exact Or.inl (walk_success_build mem p a x hp hp32 ha st st1 st' resp V' hst1 hrd hmem
        (hok ▸ hrest))
    · -- FAILURE
      have hflag0 : resp.flag = 0 := by simp [CallResponse.flag, hsucc]
      have hretV1 : VEnv.get V1 "ret" = some (0 : U256) := by
        rw [hV1, hflag0]
        exact Midfall.LoweringV3.PcsRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) hrv0
      have hrest := walk_failure_rest (c := permissive (callsOf product)) (g := g) funs p
        V V1 st st1 resp V' st' o hV1 hflag0 hst1 hpf_some ⟨rv0, hrv0⟩ hrest1
      have hok := hrest.hok
      rw [hok] at ⊢
      exact Or.inr (walk_failure_build mem p a x hp st st1 st' resp V' hst1 hmem (hok ▸ hrest))
  · obtain ⟨-, ho1, -⟩ := exec_assign_staticcall_inv (funs := funs) (gas := gas)
      (vp := BitVec.ofNat 256 p) hgp_mptr h1
    exact absurd ho1 hne1




theorem bi_prelude_main (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (rw : U256) (a e s : Nat) (succ : U256)
    (hsucc : succ ≠ 0) (hae : a + 32 < e) (hal : (e - a) % 32 = 0) (he : e < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 2 8)
      (fun V st =>
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 e) ∧
        VEnv.get V "scratch_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "r" = some rw ∧ VEnv.get V "ret" = some succ ∧
        (loadWord st.memory a).toNat < rw.toNat)
      (fun _ st V' st' o => o = .normal ∧
        VEnv.get V' "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V' "mptr_end" = some (BitVec.ofNat 256 e) ∧
        VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V' "gp" = some (loadWord st.memory a) ∧
        VEnv.get V' "r" = some rw ∧ (VEnv.get V' "ret").isSome ∧
        st'.memory = st.memory) := by
  obtain ⟨body, hform⟩ := bi_prelude_form (consts := consts)
  rw [hform]
  intro V st hpre V' st' o hrun
  obtain ⟨hstart, hend, hscratch, hr, hret, hload0⟩ := hpre
  have hae' : a < e := by omega
  have hea : a ≤ e := by omega
  have hcpos : 0 < e - a := by omega
  have hc_lt : e - a < 2 ^ 256 := by omega
  have htoNat_a : (BitVec.ofNat 256 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : a < 2 ^ 256)]
  have hsubeq : (BitVec.ofNat 256 e - BitVec.ofNat 256 a : U256) =
      BitVec.ofNat 256 (e - a) := ofNat_sub_of_le a e hea he
  -- s2
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · have h1c := exec_guard_ret0_lt_vars_false (x := "mptr_end") (y := "mptr_start")
      hend hstart (ofNat_ult_ofNat_false a e hea he) h1
    obtain ⟨-, hV1, hst1⟩ := h1c
    subst hV1
    -- s3
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨yv, zv, hyv, hzv, ho2, hV2, hst2⟩ :=
        exec_let_sub_vars_inv (x := "count_bytes") (y := "mptr_end") (z := "mptr_start") h2
      rw [hend] at hyv; rw [hstart] at hzv
      injection hyv with hy; injection hzv with hz
      subst hy hz
      rw [hsubeq] at hV2
      subst hV2
      have hget3 : VEnv.get (("count_bytes", BitVec.ofNat 256 (e - a)) :: V1) "count_bytes" =
            some (BitVec.ofNat 256 (e - a)) := by simp [VEnv.get, List.find?]
      -- s4
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · have hget3 : VEnv.get (("count_bytes", BitVec.ofNat 256 (e - a)) :: V1) "count_bytes" =
            some (BitVec.ofNat 256 (e - a)) := by simp [VEnv.get, List.find?]
        have h3c := (exec_guard_iszero_var (x := "count_bytes") hget3 h3).1
          (ofNat_ne_zero_of_pos hcpos hc_lt)
        obtain ⟨-, hV3, hst3⟩ := h3c
        subst hV3
        -- s5
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · have h4c := exec_guard_false_eq_var_lit (x := "count_bytes") (k := 32) (body := body)
            hget3 (ofNat_ne_of_ne (by omega : e - a ≠ 32) hc_lt (by norm_num : 32 < 2 ^ 256)) h4
          obtain ⟨-, hV4, hst4⟩ := h4c
          subst hV4
          -- s6
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest4 with
            ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
          · obtain ⟨v5, hget5, ho5, hV5, hst5⟩ :=
              exec_let_var_inv (x := "gp_mptr") (y := "scratch_mptr") h5
            rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "scratch_mptr") (by decide)] at hget5
            rw [hscratch] at hget5
            injection hget5 with hv5
            subst hv5 hV5
            -- s7
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest5 with
              ⟨V6, st6, h6, hrest6⟩ | ⟨h6, hne6⟩
            · obtain ⟨p6, v6, hget6, hv6, ho6, hV6, hst6⟩ :=
                exec_let_mload_var_inv (x := "gp") (y := "mptr_start") h6
              rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr_start") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "mptr_start") (by decide)] at hget6
              rw [hstart] at hget6
              injection hget6 with hp6
              subst hp6 hV6
              have hv6' : v6 = loadWord st.memory a := by
                rw [hv6, htoNat_a, hst5, hst4, hst3, hst2, hst1]
              have hlt6 : v6.toNat < rw.toNat := by rw [hv6']; exact hload0
              -- s8
              rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest6 with
                ⟨V7, st7, h7, hrest7⟩ | ⟨h7, hne7⟩
              · have hgetgp : VEnv.get (("gp", v6) ::
                    ("gp_mptr", BitVec.ofNat 256 s) ::
                    ("count_bytes", BitVec.ofNat 256 (e - a)) :: V1) "gp" = some v6 := by
                  simp [VEnv.get, List.find?]
                have hgetr : VEnv.get (("gp", v6) ::
                    ("gp_mptr", BitVec.ofNat 256 s) ::
                    ("count_bytes", BitVec.ofNat 256 (e - a)) :: V1) "r" = some rw := by
                  rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "r") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "r") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "r") (by decide)]
                  exact hr
                have h7c := exec_guard_ret0_iszero_lt_vars_false (x := "gp") (y := "r")
                  hgetgp hgetr (ult_of_toNat_lt hlt6) h7
                obtain ⟨-, hV7, hst7⟩ := h7c
                subst hV7
                -- s9
                rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest7 with
                  ⟨V8, st8, h8, hrest8⟩ | ⟨h8, hne8⟩
                · obtain ⟨v8, hget8, ho8, hV8, hst8⟩ :=
                    exec_let_add_var_lit_inv (x := "mptr") (y := "mptr_start") (k := 32) h8
                  rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr_start") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr_start") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "mptr_start") (by decide)] at hget8
                  rw [hstart] at hget8
                  injection hget8 with hv8
                  subst hv8 hV8
                  cases hrest8
                  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · -- mptr
                    simp [VEnv.get, List.find?]
                    rw [ofNat_add_32 a (by omega : a + 32 < 2 ^ 256)]
                  · -- mptr_end
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "mptr_end") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "mptr_end") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "mptr_end") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "mptr_end") (by decide)]
                    exact hend
                  · -- gp_mptr
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp_mptr") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "gp_mptr") (by decide)]
                    simp [VEnv.get, List.find?]
                  · -- gp
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "gp") (by decide)]
                    simp [VEnv.get, List.find?]
                    exact hv6'
                  · -- r
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "r") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "r") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "r") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "r") (by decide)]
                    exact hr
                  · -- ret isSome
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "mptr") (y := "ret") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "ret") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "ret") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "ret") (by decide)]
                    rw [hret]
                    rfl
                  · -- memory
                    rw [hst8, hst7, hst6, hst5, hst4, hst3, hst2, hst1]
                    rfl
                · obtain ⟨-, -, ho8, -, -⟩ := exec_let_add_var_lit_inv (x := "mptr") (y := "mptr_start") (k := 32) h8
                  exact absurd ho8 hne8
              · obtain ⟨ho7, -, -⟩ := (exec_guard_ret0_iszero_lt_vars_false (x := "gp") (y := "r")
                  (by simp [VEnv.get, List.find?])
                  (by
                    rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp") (y := "r") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "gp_mptr") (y := "r") (by decide),
                      Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "count_bytes") (y := "r") (by decide)]
                    exact hr)
                  (ult_of_toNat_lt hlt6) h7)
                exact absurd ho7 hne7
            · obtain ⟨-, -, -, -, ho6, -, -⟩ := exec_let_mload_var_inv (x := "gp") (y := "mptr_start") h6
              exact absurd ho6 hne6
          · obtain ⟨-, -, ho5, -, -⟩ := exec_let_var_inv (x := "gp_mptr") (y := "scratch_mptr") h5
            exact absurd ho5 hne5
        · obtain ⟨ho4, -, -⟩ := exec_guard_false_eq_var_lit (x := "count_bytes") (k := 32) (body := body)
            hget3 (ofNat_ne_of_ne (by omega : e - a ≠ 32) hc_lt (by norm_num : 32 < 2 ^ 256)) h4
          exact absurd ho4 hne4
      · obtain ⟨ho3, -, -⟩ := (exec_guard_iszero_var (x := "count_bytes") hget3 h3).1
          (ofNat_ne_zero_of_pos hcpos hc_lt)
        exact absurd ho3 hne3
    · obtain ⟨-, -, -, -, ho2, -, -⟩ :=
        exec_let_sub_vars_inv (x := "count_bytes") (y := "mptr_end") (z := "mptr_start") h2
      exact absurd ho2 hne2
  · have h1c := exec_guard_ret0_lt_vars_false (x := "mptr_end") (y := "mptr_start")
      hend hstart (ofNat_ult_ofNat_false a e hea he) h1
    obtain ⟨ho1, -, -⟩ := h1c
    exact absurd ho1 hne1


theorem wMulmodAt_zmod_inv (x : U256) (hx0 : x.toNat ≠ 0) (hx : x.toNat < Midfall.Yul.blsR) :
    Midfall.LoweringV3.QuotientRows.wMulmodAt (BitVec.ofNat 256 ((x.toNat : ZMod Midfall.Yul.blsR)⁻¹).val) x
      (BitVec.ofNat 256 Midfall.Yul.blsR) = 1 := by
  have hR : (BitVec.ofNat 256 Midfall.Yul.blsR : U256) ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : Midfall.Yul.blsR < 2 ^ 256)] at this
    simp at this
    have hpos : 0 < Midfall.Yul.blsR := by decide
    omega
  rw [Midfall.LoweringV3.QuotientRows.wMulmodAt, if_neg hR]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (zmod_inv_val_lt x),
    Nat.mod_eq_of_lt (by decide : Midfall.Yul.blsR < 2 ^ 256)]
  haveI : Fact (1 < Midfall.Yul.blsR) := ⟨by decide⟩
  have hxne : (x.toNat : ZMod Midfall.Yul.blsR) ≠ 0 := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx, ZMod.val_zero] at this
    exact hx0 this
  have hinv : (x.toNat : ZMod Midfall.Yul.blsR) * ((x.toNat : ZMod Midfall.Yul.blsR)⁻¹) = 1 :=
    mul_inv_cancel₀ hxne
  have hval := congrArg ZMod.val hinv
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_eq_of_lt hx, ZMod.val_one] at hval
  rw [Nat.mul_comm] at hval
  rw [hval]
  rfl

theorem fwdProd_zmod_inv (mem : Nat → UInt8) (a k : Nat)
    (hx0 : (fwdProd mem a (BitVec.ofNat 256 Midfall.Yul.blsR) (k - 1)).toNat ≠ 0)
    (hx : (fwdProd mem a (BitVec.ofNat 256 Midfall.Yul.blsR) (k - 1)).toNat < Midfall.Yul.blsR) :
    Midfall.LoweringV3.QuotientRows.wMulmodAt (BitVec.ofNat 256
        (((fwdProd mem a (BitVec.ofNat 256 Midfall.Yul.blsR) (k - 1)).toNat :
          ZMod Midfall.Yul.blsR)⁻¹).val)
      (fwdProd mem a (BitVec.ofNat 256 Midfall.Yul.blsR) (k - 1))
      (BitVec.ofNat 256 Midfall.Yul.blsR) = 1 :=
  wMulmodAt_zmod_inv _ hx0 hx


theorem ofNat_sub_two_blsR :
    ((BitVec.ofNat 256 Midfall.Yul.blsR : U256) - 2) =
      BitVec.ofNat 256 (Midfall.Yul.blsR - 2) := by
  apply BitVec.eq_of_toNat_eq
  have hb : (BitVec.ofNat 256 Midfall.Yul.blsR : U256).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  have h2 : (2 : U256).toNat = 2 := rfl
  have hb2 : (BitVec.ofNat 256 (Midfall.Yul.blsR - 2) : U256).toNat = Midfall.Yul.blsR - 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  rw [BitVec.toNat_sub, hb, h2, hb2]
  have hbge : 2 ≤ Midfall.Yul.blsR := by decide
  have hb_lt : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have hsum : 2 ^ 256 - 2 + Midfall.Yul.blsR = 2 ^ 256 + (Midfall.Yul.blsR - 2) := by omega
  rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : Midfall.Yul.blsR - 2 < 2 ^ 256)]



theorem bi_bridge_stores (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (p : Nat) (gv : U256) (hp : p + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 15 6)
      (fun V st =>
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V "gp" = some gv ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR))
      (fun V0 st V' st' o => o = .normal ∧ V' = V0 ∧
        st'.memory = mxMem st.memory p gv) := by
  rw [bi_bridge_stores_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hgp_mptr, hg, hr⟩ := hpre
  have hval32 : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.ylit 32) (.vals [vv] st1)) → st1 = st0 := by
    intro st0 st1 h
    obtain ⟨vv, hvv⟩ := h
    obtain ⟨-, hst⟩ := eval_lit_inv hvv
    exact hst
  have hvchar32 : ∀ vv st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.ylit 32) (.vals [vv] st1) → vv = 32 := by
    intro vv st0 st1 h
    obtain ⟨hv, -⟩ := eval_lit_inv h
    exact hv
  have hne32 : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.ylit 32) (.halt st1) → False := by
    intro st0 st1 h
    exact Midfall.LoweringV2.Blocks.VkLoading.vkLit_ne_halts h
  have hvalg : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "gp") (.vals [vv] st1)) → st1 = st0 := by
    intro st0 st1 h
    obtain ⟨vv, hvv⟩ := h
    obtain ⟨-, hst⟩ := eval_var_inv hvv
    exact hst
  have hvcharg : ∀ vv st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "gp") (.vals [vv] st1) → vv = gv := by
    intro vv st0 st1 h
    obtain ⟨hget, -⟩ := eval_var_inv h
    rw [hg] at hget
    injection hget with hv
    exact hv.symm
  have hneg : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "gp") (.halt st1) → False := by
    intro st0 st1 h
    exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts h
  have hvalr : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "r") (.vals [vv] st1)) → st1 = st0 := by
    intro st0 st1 h
    obtain ⟨vv, hvv⟩ := h
    obtain ⟨-, hst⟩ := eval_var_inv hvv
    exact hst
  have hvcharr : ∀ vv st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "r") (.vals [vv] st1) → vv = BitVec.ofNat 256 Midfall.Yul.blsR := by
    intro vv st0 st1 h
    obtain ⟨hget, -⟩ := eval_var_inv h
    rw [hr] at hget
    injection hget with hv
    exact hv.symm
  have hner : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yvar "r") (.halt st1) → False := by
    intro st0 st1 h
    exact Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts h
  have hvalsub : ∀ st0 st1, (∃ vv, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2]) (.vals [vv] st1)) → st1 = st0 := by
    intro st0 st1 h
    obtain ⟨vv, hvv⟩ := h
    obtain ⟨-, -, -, hst⟩ := eval_sub_var_lit_inv (y := "r") (k := 2) hvv
    exact hst
  have hvcharsub : ∀ vv st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2]) (.vals [vv] st1) →
      vv = BitVec.ofNat 256 (Midfall.Yul.blsR - 2) := by
    intro vv st0 st1 h
    obtain ⟨a, hget, hv, -⟩ := eval_sub_var_lit_inv (y := "r") (k := 2) h
    rw [hr] at hget
    injection hget with ha
    subst ha
    rw [hv]
    exact ofNat_sub_two_blsR
  have hnesub : ∀ st0 st1, EvalExpr (Bridge.Dialect c g) funs V st0
      (GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2]) (.halt st1) → False := by
    intro st0 st1 h
    exact eval_sub_var_lit_no_halt (y := "r") (k := 2) h
  -- s15
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨xv, hxv, -, hV1, hst1⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 0)
      (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h1
    rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
    rw [ofNat_add_ofNat_toNat p 0 (by omega), Nat.add_zero] at hst1
    rw [hV1] at hrest1
    -- s16
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨xv, hxv, -, hV2, hst2⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 32)
        (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h2
      rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
      rw [ofNat_add_ofNat_toNat p 32 (by omega)] at hst2
      rw [hV2] at hrest2
      -- s17
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨xv, hxv, -, hV3, hst3⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 64)
          (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h3
        rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
        rw [ofNat_add_ofNat_toNat p 64 (by omega)] at hst3
        rw [hV3] at hrest3
        -- s18
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨xv, hxv, -, hV4, hst4⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 96)
            (val := GenAst.yvar "gp") (v0 := gv) hvalg hvcharg hneg h4
          rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
          rw [ofNat_add_ofNat_toNat p 96 (by omega)] at hst4
          rw [hV4] at hrest4
          -- s19
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest4 with
            ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
          · obtain ⟨xv, hxv, -, hV5, hst5⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 128)
              (val := GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2])
              (v0 := BitVec.ofNat 256 (Midfall.Yul.blsR - 2)) hvalsub hvcharsub hnesub h5
            rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
            rw [ofNat_add_ofNat_toNat p 128 (by omega)] at hst5
            rw [hV5] at hrest5
            -- s20
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest5 with
              ⟨V6, st6, h6, hrest6⟩ | ⟨h6, hne6⟩
            · obtain ⟨xv, hxv, ho, hV, hst6⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 160)
                (val := GenAst.yvar "r") (v0 := BitVec.ofNat 256 Midfall.Yul.blsR) hvalr hvcharr hner h6
              rw [hgp_mptr] at hxv; injection hxv with hx; subst hx
              rw [ofNat_add_ofNat_toNat p 160 (by omega)] at hst6
              cases hrest6
              refine ⟨rfl, hV, ?_⟩
              rw [hst6, hst5, hst4, hst3, hst2, hst1]
              rfl
            · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 160)
                (val := GenAst.yvar "r") (v0 := BitVec.ofNat 256 Midfall.Yul.blsR) hvalr hvcharr hner h6
              exact absurd ho hne6
          · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 128)
              (val := GenAst.yop EVM.Op.sub [GenAst.yvar "r", GenAst.ylit 2])
              (v0 := BitVec.ofNat 256 (Midfall.Yul.blsR - 2)) hvalsub hvcharsub hnesub h5
            exact absurd ho hne5
        · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 96)
            (val := GenAst.yvar "gp") (v0 := gv) hvalg hvcharg hneg h4
          exact absurd ho hne4
      · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 64)
          (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h3
        exact absurd ho hne3
    · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 32)
        (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h2
      exact absurd ho hne2
  · obtain ⟨-, -, ho, -, -⟩ := exec_mstore_add_var_inv_val (x := "gp_mptr") (k := 0)
      (val := GenAst.ylit 32) (v0 := 32) hval32 hvchar32 hne32 h1
    exact absurd ho hne1


theorem bi_bridge_head_form (consts : Inline.Consts) :
    seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 4 =
      [GenAst.ylet "x_last" (GenAst.yop EVM.Op.mload [GenAst.yvar "mptr"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero
          [GenAst.yop EVM.Op.lt [GenAst.yvar "x_last", GenAst.yvar "r"]])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave],
        GenAst.yset "gp" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "gp", GenAst.yvar "x_last", GenAst.yvar "r"]),
        GenAst.yif (GenAst.yop EVM.Op.iszero [GenAst.yvar "gp"])
          [GenAst.yset "ret" (GenAst.ylit 0), Stmt.leave]] := by
  kernel_rfl

theorem bi_bridge_head (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (p a mp : Nat) (gv x_last : U256) (hmp : mp < 2 ^ 256)
    (hprime : Nat.Prime Midfall.Yul.blsR)
    (hg0 : gv ≠ 0) (hg_lt : gv.toNat < Midfall.Yul.blsR)
    (hx0 : x_last ≠ 0) (hxlt : x_last.toNat < Midfall.Yul.blsR) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 4)
      (fun V st =>
        VEnv.get V "mptr" = some (BitVec.ofNat 256 mp) ∧
        VEnv.get V "gp" = some gv ∧
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        (VEnv.get V "ret").isSome ∧
        (VEnv.get V "precompile_failed").isSome ∧
        loadWord st.memory mp = x_last)
      (fun _ st V' st' o => o = .normal ∧
        VEnv.get V' "gp" = some (Midfall.LoweringV3.QuotientRows.wMulmodAt gv x_last
          (BitVec.ofNat 256 Midfall.Yul.blsR)) ∧
        VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V' "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        (VEnv.get V' "ret").isSome ∧
        (VEnv.get V' "precompile_failed").isSome ∧
        st'.memory = st.memory) := by
  rw [bi_bridge_head_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hmptr, hg, hgp_mptr, hmstart, hr, hret, hpf, hload⟩ := hpre
  have htoNat_blsR : (BitVec.ofNat 256 Midfall.Yul.blsR).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  have hprime' : Nat.Prime (BitVec.ofNat 256 Midfall.Yul.blsR).toNat := by rwa [htoNat_blsR]
  have hxult : x_last.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = true := by
    apply ult_of_toNat_lt
    rw [htoNat_blsR]; exact hxlt
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨p11, v11, hget11, hv11, -, hV1, hst1⟩ :=
      exec_let_mload_var_inv (x := "x_last") (y := "mptr") h1
    rw [hmptr] at hget11
    injection hget11 with hp11; subst hp11
    rw [show (BitVec.ofNat 256 mp).toNat = mp from by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmp]] at hv11
    rw [hload] at hv11
    subst hV1
    have hxult' : v11.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = true := by rw [hv11]; exact hxult
    have hx0' : v11 ≠ 0 := by rw [hv11]; exact hx0
    have hxlt' : v11.toNat < Midfall.Yul.blsR := by rw [hv11]; exact hxlt
    have hgetxl : VEnv.get (("x_last", v11) :: V) "x_last" = some v11 := by
      simp [VEnv.get, List.find?]
    have hgetr1 : VEnv.get (("x_last", v11) :: V) "r" =
        some (BitVec.ofNat 256 Midfall.Yul.blsR) := by
      rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
        (x := "x_last") (y := "r") (by decide)]
      exact hr
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · have h2c := exec_guard_ret0_iszero_lt_vars_false (x := "x_last") (y := "r")
        hgetxl hgetr1 hxult' h2
      obtain ⟨-, hV2, hst2⟩ := h2c
      subst hV2
      have hgetg : VEnv.get (("x_last", v11) :: V) "gp" = some gv := by
        rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
          (x := "x_last") (y := "gp") (by decide)]
        exact hg
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · have h3c := exec_assign_mulmod_vars_inv (x := "gp") (y := "x_last") (z := "r")
          hgetg hgetxl hgetr1 h3
        obtain ⟨-, hV3, hst3⟩ := h3c
        subst hV3
        have hgpne : Midfall.LoweringV3.QuotientRows.wMulmodAt gv v11
            (BitVec.ofNat 256 Midfall.Yul.blsR) ≠ 0 :=
          (wMulmodAt_ne_zero_iff hprime' hg_lt hxlt').mpr ⟨hg0, hx0'⟩
        have hgetgp3 : VEnv.get (VEnv.set (("x_last", v11) :: V) "gp"
            (Midfall.LoweringV3.QuotientRows.wMulmodAt gv v11
              (BitVec.ofNat 256 Midfall.Yul.blsR))) "gp" =
            some (Midfall.LoweringV3.QuotientRows.wMulmodAt gv v11
              (BitVec.ofNat 256 Midfall.Yul.blsR)) :=
          Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect c g) hgetg
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · have h4c := exec_guard_ret0_iszero_var_false (x := "gp") hgetgp3 hgpne h4
          obtain ⟨ho4, hV4, hst4⟩ := h4c
          subst hV4
          cases hrest4
          have hstoremem : st'.memory = st.memory := by
            rw [hst4, hst3, hst2, hst1]; rfl
          refine ⟨ho4, ?_, ?_, ?_, ?_, ?_, ?_, hstoremem⟩
          · rw [hgetgp3, hv11]
          · rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "gp") (y := "gp_mptr") (by decide),
              Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x_last") (y := "gp_mptr") (by decide)]
            exact hgp_mptr
          · rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "gp") (y := "mptr_start") (by decide),
              Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x_last") (y := "mptr_start") (by decide)]
            exact hmstart
          · rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "gp") (y := "r") (by decide)]
            exact hgetr1
          · rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "gp") (y := "ret") (by decide),
              Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x_last") (y := "ret") (by decide)]
            rw [hret]
          · rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "gp") (y := "precompile_failed") (by decide),
              Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x_last") (y := "precompile_failed") (by decide)]
            rw [hpf]
        · obtain ⟨ho4, -, -⟩ := exec_guard_ret0_iszero_var_false (x := "gp") hgetgp3 hgpne h4
          exact absurd ho4 hne4
      · obtain ⟨ho3, -, -⟩ := exec_assign_mulmod_vars_inv (x := "gp") (y := "x_last") (z := "r")
          hgetg hgetxl hgetr1 h3
        exact absurd ho3 hne3
    · obtain ⟨ho2, -, -⟩ := exec_guard_ret0_iszero_lt_vars_false (x := "x_last") (y := "r")
        hgetxl hgetr1 hxult' h2
      exact absurd ho2 hne2
  · obtain ⟨-, -, -, -, ho1, -, -⟩ := exec_let_mload_var_inv (x := "x_last") (y := "mptr") h1
    exact absurd ho1 hne1

set_option maxHeartbeats 500000 in


theorem bi_bridge_contract (consts : Inline.Consts) (funs : FunEnv (Bridge.Dialect c g))
    (p a mp : Nat) (gv x_last : U256)
    (hp : p + 192 < 2 ^ 256) (hmp : mp < 2 ^ 256)
    (hprime : Nat.Prime Midfall.Yul.blsR)
    (hg0 : gv ≠ 0) (hg_lt : gv.toNat < Midfall.Yul.blsR)
    (hx0 : x_last ≠ 0) (hxlt : x_last.toNat < Midfall.Yul.blsR) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 10)
      (fun V st =>
        VEnv.get V "mptr" = some (BitVec.ofNat 256 mp) ∧
        VEnv.get V "gp" = some gv ∧
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        (VEnv.get V "ret").isSome ∧
        (VEnv.get V "precompile_failed").isSome ∧
        loadWord st.memory mp = x_last)
      (fun _ st V' st' o => o = .normal ∧
        VEnv.get V' "gp" = some (Midfall.LoweringV3.QuotientRows.wMulmodAt gv x_last (BitVec.ofNat 256 Midfall.Yul.blsR)) ∧
        VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 p) ∧
        VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V' "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        (VEnv.get V' "ret").isSome ∧
        (VEnv.get V' "precompile_failed").isSome ∧
        st'.memory = mxMem st.memory p (Midfall.LoweringV3.QuotientRows.wMulmodAt gv x_last (BitVec.ofNat 256 Midfall.Yul.blsR))) := by
  let gp' : U256 := Midfall.LoweringV3.QuotientRows.wMulmodAt gv x_last (BitVec.ofNat 256 Midfall.Yul.blsR)
  have hform : seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 10 =
      seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 11 4 ++
        seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 15 6 := by
    rw [bi_bridge_form, bi_bridge_head_form, bi_bridge_stores_form]
  rw [hform]
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
  · have hh := bi_bridge_head (c := c) (g := g) (consts := consts) funs p a mp gv x_last
      hmp hprime hg0 hg_lt hx0 hxlt V st hpre V1 st1 .normal hhead
    obtain ⟨-, hgp1, hgpm1, hms1, hr1, hret1, hpf1, hmem1⟩ := hh
    obtain ⟨ho, hV', hmem⟩ :=
      bi_bridge_stores (c := c) (g := g) (consts := consts) funs p gp' hp V1 st1
        ⟨hgpm1, hgp1, hr1⟩ V' st' o htail
    refine ⟨ho, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hV']; exact hgp1
    · rw [hV']; exact hgpm1
    · rw [hV']; exact hms1
    · rw [hV']; exact hr1
    · rw [hV']; exact hret1
    · rw [hV']; exact hpf1
    · calc st'.memory = mxMem st1.memory p gp' := hmem
        _ = mxMem st.memory p (Midfall.LoweringV3.QuotientRows.wMulmodAt gv x_last (BitVec.ofNat 256 Midfall.Yul.blsR)) := by
          rw [hmem1]
  · exact absurd (bi_bridge_head (c := c) (g := g) (consts := consts) funs p a mp gv x_last
      hmp hprime hg0 hg_lt hx0 hxlt V st hpre V' st' o hhead).1 hne


theorem exec_guard_var_body {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    {x : String} {rv : U256} {body : Block EVM.Op}
    (hx : VEnv.get V x = some rv)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.var x) body) V' st' o) :
    (rv ≠ 0 → ExecStmt (Bridge.Dialect c g) funs V st (Stmt.block body) V' st' o) ∧
      (rv = 0 → o = .normal ∧ V' = V ∧ st' = st) := by
  constructor
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨hget, hst⟩ := eval_var_inv hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        subst hst
        exact hbody
    | ifFalse hc hz =>
        obtain ⟨hget, -⟩ := eval_var_inv hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        exact absurd hz hrv
    | ifHalt hc => exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hc).elim
  · intro hrv
    cases h with
    | ifTrue hc hnz hbody =>
        obtain ⟨hget, -⟩ := eval_var_inv hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        subst hrv
        exact absurd rfl hnz
    | ifFalse hc hz =>
        obtain ⟨hget, hst⟩ := eval_var_inv hc
        rw [hx] at hget
        injection hget with hv
        subst hv
        exact ⟨rfl, rfl, hst⟩
    | ifHalt hc => exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hc).elim

theorem mxMem_outside (mem : Nat → UInt8) (p : Nat) (x : U256) (q : Nat)
    (h : q < p ∨ p + 192 ≤ q) : mxMem mem p x q = mem q := by
  simp only [mxMem]
  rw [Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p + 160 ∨ p + 160 + 32 ≤ q),
    Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p + 128 ∨ p + 128 + 32 ≤ q),
    Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p + 96 ∨ p + 96 + 32 ≤ q),
    Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p + 64 ∨ p + 64 + 32 ≤ q),
    Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p + 32 ∨ p + 32 + 32 ≤ q),
    Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega : q < p ∨ p + 32 ≤ q)]

theorem copyReturn_outside' (mem : Nat → UInt8) (dst size : Nat) (dat : List UInt8) (x : Nat)
    (h : x < dst ∨ dst + min size dat.length ≤ x) : copyReturn mem dst size dat x = mem x := by
  simp only [copyReturn]
  rw [if_neg]
  omega

theorem eval_staticcall_args_var {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {gas : Nat} {vp : U256} (v : String)
    (hgp : VEnv.get V v = some vp)
    {vs : List U256} {st' : EvmState}
    (h : EvalArgs (Bridge.Dialect c g) funs V st
      [Expr.lit (Literal.number gas), Expr.lit (Literal.number 5), Expr.var v,
       Expr.lit (Literal.number 192), Expr.var v, Expr.lit (Literal.number 32)]
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

theorem exec_assign_staticcall_var_inv {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {gas : Nat} {vp : U256} (v : String)
    (hgp : VEnv.get V v = some vp)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["ret"] (Expr.builtin EVM.Op.staticcall
        [Expr.lit (Literal.number gas), Expr.lit (Literal.number 5), Expr.var v,
         Expr.lit (Literal.number 192), Expr.var v, Expr.lit (Literal.number 32)]))
      V' st' o) :
    ∃ resp, o = .normal ∧ c.Call
      { kind := .staticcall, gas := BitVec.ofNat 256 gas, target := BitVec.ofNat 256 5,
        value := 0, input := readBytes st.memory vp.toNat 192 } st resp ∧
      V' = VEnv.set V "ret" resp.flag ∧
      st' = finishCall .staticcall st resp vp.toNat 192 vp.toNat 32 := by
  cases h with
  | assignVal he hlen =>
      obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv he
      obtain ⟨hvs, hst⟩ := eval_staticcall_args_var v hgp hargs
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
          obtain ⟨hvs, -⟩ := eval_staticcall_args_var v hgp hargs
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
            · exact Or.inr ⟨v, rfl⟩
            · exact Or.inl ⟨192, rfl⟩
            · exact Or.inr ⟨v, rfl⟩
            · exact Or.inl ⟨32, rfl⟩) hargs).elim


theorem exec_mstore_var_mload_mem {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {x y : String}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.var x, Expr.builtin Op.mload [Expr.var y]])) V' st' o) :
    ∃ xv yv, VEnv.get V x = some xv ∧ VEnv.get V y = some yv ∧ o = .normal ∧
      V' = V ∧ st'.memory = storeWord st.memory xv.toNat (loadWord st.memory yv.toNat) ∧
      st'.env = st.env ∧ st'.halted = st.halted := by
  cases h with
  | exprStmt he =>
      obtain ⟨argvals, st1, hargs, hbi⟩ := eval_builtin_vals_inv he
      cases hargs with
      | argsCons hrest hx =>
          cases hx with
          | var hxv =>
              cases hrest with
              | argsCons hnil hval =>
                  cases hnil with
                  | argsNil =>
                      obtain ⟨p, hy, hv, hstm⟩ := eval_mload_var_inv hval
                      subst hstm
                      simp only [builtinWithExternal, stepOp] at hbi
                      cases hbi
                      refine ⟨_, _, hxv, hy, rfl, rfl, ?_, rfl, rfl⟩
                      rw [Midfall.LoweringV3.ModexpGeneral.touchMemory_memory, hv]
  | exprStmtHalt he =>
      cases he with
      | builtinHalt hargs hbi =>
          simp only [builtinWithExternal, stepOp] at hbi
          split at hbi <;> simp at hbi
      | builtinArgsHalt hargs =>
          cases hargs with
          | argsRestHalt h' =>
              cases h' with
              | argsRestHalt h'' => cases h''
              | argsHeadHalt _ hval => exact (eval_mload_var_halt_false hval).elim
          | argsHeadHalt _ hx => exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hx).elim


theorem modexpFrameStores_single_contract (funs : FunEnv (Bridge.Dialect c g)) (pv xv fv : U256)
    (hbound : pv.toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "single_scratch" (Expr.var "x") (Expr.var "r")
        Midfall.Generator.templateConstantsDefault)
      (fun V st => VEnv.get V "single_scratch" = some pv ∧ VEnv.get V "x" = some xv ∧
        VEnv.get V "r" = some fv)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧
        st'.memory = mxMemFr st.memory pv.toNat xv fv ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx, hfr⟩ := hpre
  simp only [GenAst.modexpFrameStores, Midfall.Generator.templateConstantsDefault,
    GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.ylit] at hrun
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
      ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨hV1, hmem1, henv1, hhalt1⟩ :=
      exec_mstore_state (c := c) (g := g) funs h1
        (fun stV v hv => (eval_lit_eq funs V (st := st) 32 hv).2)
        (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 0 pv hp ha).2)
        (fun stA a ha => (eval_add_var_lit funs V (st := st) "single_scratch" 0 pv hp ha).1)
        (fun stV v hv => (eval_lit_eq funs V (st := st) 32 hv).1)
    subst V1
    rw [toNat_add_ofNat pv 0 (by omega)] at hmem1
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
        ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨hV2, hmem2, henv2, hhalt2⟩ :=
        exec_mstore_state (c := c) (g := g) funs h2
          (fun stV v hv => (eval_lit_eq funs V (st := st1) 32 hv).2)
          (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 32 pv hp ha).2)
          (fun stA a ha => (eval_add_var_lit funs V (st := st1) "single_scratch" 32 pv hp ha).1)
          (fun stV v hv => (eval_lit_eq funs V (st := st1) 32 hv).1)
      subst V2
      rw [toNat_add_ofNat pv 32 (by omega)] at hmem2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
          ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · obtain ⟨hV3, hmem3, henv3, hhalt3⟩ :=
          exec_mstore_state (c := c) (g := g) funs h3
            (fun stV v hv => (eval_lit_eq funs V (st := st2) 32 hv).2)
            (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 64 pv hp ha).2)
            (fun stA a ha => (eval_add_var_lit funs V (st := st2) "single_scratch" 64 pv hp ha).1)
            (fun stV v hv => (eval_lit_eq funs V (st := st2) 32 hv).1)
        subst V3
        rw [toNat_add_ofNat pv 64 (by omega)] at hmem3
        rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
            ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · obtain ⟨hV4, hmem4, henv4, hhalt4⟩ :=
            exec_mstore_state (c := c) (g := g) funs h4
              (fun stV v hv => (eval_var_eq funs V (st := st3) "x" xv hx hv).2)
              (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 96 pv hp ha).2)
              (fun stA a ha => (eval_add_var_lit funs V (st := st3) "single_scratch" 96 pv hp ha).1)
              (fun stV v hv => (eval_var_eq funs V (st := st3) "x" xv hx hv).1)
          subst V4
          rw [toNat_add_ofNat pv 96 (by omega)] at hmem4
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest4 with
              ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
          · obtain ⟨hV5, hmem5, henv5, hhalt5⟩ :=
              exec_mstore_state (c := c) (g := g) funs h5
                (fun stV v hv => (eval_sub_var_lit funs V (st := st4) "r" 2 fv hfr hv).2)
                (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 128 pv hp ha).2)
                (fun stA a ha => (eval_add_var_lit funs V (st := st4) "single_scratch" 128 pv hp ha).1)
                (fun stV v hv => (eval_sub_var_lit funs V (st := st4) "r" 2 fv hfr hv).1)
            subst V5
            rw [toNat_add_ofNat pv 128 (by omega)] at hmem5
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest5 with
                ⟨V6, st6, h6, hrest6⟩ | ⟨h6, hne6⟩
            · obtain ⟨hV6, hmem6, henv6, hhalt6⟩ :=
                exec_mstore_state (c := c) (g := g) funs h6
                  (fun stV v hv => (eval_var_eq funs V (st := st5) "r" fv hfr hv).2)
                  (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "single_scratch" 160 pv hp ha).2)
                  (fun stA a ha => (eval_add_var_lit funs V (st := st5) "single_scratch" 160 pv hp ha).1)
                  (fun stV v hv => (eval_var_eq funs V (st := st5) "r" fv hfr hv).1)
              subst V6
              rw [toNat_add_ofNat pv 160 (by omega)] at hmem6
              cases hrest6
              refine ⟨rfl, rfl, ?_, ?_, ?_⟩
              · rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
                simp [mxMemFr]
              · rw [henv6, henv5, henv4, henv3, henv2, henv1]
              · rw [hhalt6, hhalt5, hhalt4, hhalt3, hhalt2, hhalt1]
            · exact absurd (exec_mstore_normal funs h6
                (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 160) hh)
                (fun s₁ s₂ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprVar_ne_halts hh)) hne6
          · exact absurd (exec_mstore_normal funs h5
              (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 128) hh)
              (fun s₁ s₂ hh => expr_sub_var_lit_ne_halts funs V (st := s₁) (x := "r") (n := 2) hh)) hne5
        · exact absurd (exec_mstore_normal funs h4
            (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 96) hh)
            (fun s₁ s₂ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprVar_ne_halts hh)) hne4
      · exact absurd (exec_mstore_normal funs h3
          (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 64) hh)
          (fun s₁ s₂ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprLit_ne_halts hh)) hne3
    · exact absurd (exec_mstore_normal funs h2
        (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 32) hh)
        (fun s₁ s₂ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprLit_ne_halts hh)) hne2
  · exact absurd (exec_mstore_normal funs h1
      (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "single_scratch") (n := 0) hh)
      (fun s₁ s₂ hh => Midfall.LoweringV2.Blocks.TraceReturn.trExprLit_ne_halts hh)) hne1

theorem modexpFrameStores_single_mxMem (funs : FunEnv (Bridge.Dialect c g)) (pv xv : U256)
    (hbound : pv.toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "single_scratch" (Expr.var "x") (Expr.var "r")
        Midfall.Generator.templateConstantsDefault)
      (fun V st => VEnv.get V "single_scratch" = some pv ∧ VEnv.get V "x" = some xv ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR))
      (fun V st V' st' o => o = .normal ∧ V' = V ∧
        st'.memory = mxMem st.memory pv.toNat xv ∧
        st'.env = st.env ∧ st'.halted = st.halted) := by
  intro V st hpre V' st' o hrun
  obtain ⟨hp, hx, hfr⟩ := hpre
  have h := modexpFrameStores_single_contract funs pv xv (BitVec.ofNat 256 Midfall.Yul.blsR) hbound
    V st ⟨hp, hx, hfr⟩ V' st' o hrun
  obtain ⟨ho, hV, hmem, henv, hhalt⟩ := h
  refine ⟨ho, hV, ?_, henv, hhalt⟩
  rw [hmem, mxMemFr_blsR]


theorem bi_single_head_contract (funs : FunEnv (Bridge.Dialect c g))
    (succ : U256) (a s : Nat) (ha : a + 32 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      biSingleHead
      (fun V st =>
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "scratch_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        VEnv.get V "ret" = some succ ∧
        VEnv.get V "precompile_failed" = some 0)
      (fun V0 st V' st' o =>
        (o = .normal ∧
          VEnv.get V' "x" = some (loadWord st.memory a) ∧
          VEnv.get V' "single_scratch" = some (BitVec.ofNat 256 s) ∧
          (loadWord st.memory a).toNat < Midfall.Yul.blsR ∧
          loadWord st.memory a ≠ 0 ∧
          VEnv.get V' "mptr_start" = some (BitVec.ofNat 256 a) ∧
          VEnv.get V' "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
          VEnv.get V' "ret" = some succ ∧
          VEnv.get V' "precompile_failed" = some 0 ∧
          st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          V' = ("single_scratch", BitVec.ofNat 256 s) :: ("x", loadWord st.memory a) :: V0)
        ∨ (o = .leave ∧
          VEnv.get V' "ret" = some 0 ∧
          VEnv.get V' "precompile_failed" = some 0 ∧
          st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          V' = VEnv.set (("x", loadWord st.memory a) :: V0) "ret" 0)) := by
  rw [biSingleHead]
  intro V st hpre V' st' o hrun
  obtain ⟨hmstart, hscratch, hr, hret, hpf0⟩ := hpre
  have hbR : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have htoNatR : (BitVec.ofNat 256 Midfall.Yul.blsR).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR]
  have ha_toNat : (BitVec.ofNat 256 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨p11, v11, hget11, hv11, -, hV1, hst1⟩ :=
      exec_let_mload_var_inv (x := "x") (y := "mptr_start") h1
    rw [hmstart] at hget11
    injection hget11 with hp11
    subst hp11
    rw [ha_toNat] at hv11
    subst hV1
    have hgetx : VEnv.get (("x", v11) :: V) "x" = some v11 := rfl
    have hgetr1 : VEnv.get (("x", v11) :: V) "r" =
        some (BitVec.ofNat 256 Midfall.Yul.blsR) := by
      rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "r") (by decide)]
      exact hr
    have hgetret1 : VEnv.get (("x", v11) :: V) "ret" = some succ := by
      rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g) (x := "x") (y := "ret") (by decide)]
      exact hret
    -- guard1: if iszero(lt(x,r))
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · have h2c := exec_guard_iszero_lt_reject (funs := funs)
        (x := "x") (y := "r") hgetx hgetr1 h2
      have hxlt : v11.toNat < Midfall.Yul.blsR := by
        by_contra hnot
        have hultf : v11.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = false := by
          rw [BitVec.ult]
          exact decide_eq_false (by rwa [htoNatR])
        obtain ⟨ho2, -, -⟩ := h2c.2 hultf
        exact absurd ho2 (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)
      have hult : v11.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = true := by
        apply ult_of_toNat_lt
        rwa [htoNatR]
      obtain ⟨-, hV2, hst2⟩ := h2c.1 hult
      subst hV2
      -- guard2
      rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · have h3c := exec_guard_iszero_reject (funs := funs) (x := "x") hgetx h3
        by_cases hxzero : v11 = 0
        · obtain ⟨ho3, -, -⟩ := h3c.2 hxzero
          exact absurd ho3 (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)
        · obtain ⟨-, hV3, hst3⟩ := h3c.1 hxzero
          subst hV3
          -- single_scratch let
          rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest3 with
            ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
          · obtain ⟨v4, hget4, -, hV4, hst4⟩ :=
              exec_let_var_inv (x := "single_scratch") (y := "scratch_mptr") h4
            rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x") (y := "scratch_mptr") (by decide)] at hget4
            rw [hscratch] at hget4
            injection hget4 with hv4
            subst hv4 hV4
            cases hrest4
            have hstmem : st'.memory = st.memory := by rw [hst4, hst3, hst2, hst1]; rfl
            have hstenv : st'.env = st.env := by rw [hst4, hst3, hst2, hst1]; rfl
            have hsthalt : st'.halted = st.halted := by rw [hst4, hst3, hst2, hst1]; rfl
            refine Or.inl ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hstmem, hstenv, hsthalt, by rw [hv11]⟩
            · rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "single_scratch") (y := "x") (by decide), ← hv11]
              exact hgetx
            · rw [← hv11]; exact hxlt
            · rw [← hv11]
              exact hxzero
            · rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "single_scratch") (y := "mptr_start") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "x") (y := "mptr_start") (by decide)]
              exact hmstart
            · rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "single_scratch") (y := "r") (by decide)]
              exact hgetr1
            · rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "single_scratch") (y := "ret") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "x") (y := "ret") (by decide)]
              exact hret
            · rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "single_scratch") (y := "precompile_failed") (by decide),
                Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
                (x := "x") (y := "precompile_failed") (by decide)]
              exact hpf0
          · obtain ⟨-, -, ho4, -, -⟩ :=
              exec_let_var_inv (x := "single_scratch") (y := "scratch_mptr") h4
            exact absurd ho4 hne4
      · -- guard2 non-normal: must be x = 0
        have h3c := exec_guard_iszero_reject (funs := funs) (x := "x") hgetx h3
        have hxzero : v11 = 0 := by
          by_contra hne0
          obtain ⟨ho3, -, -⟩ := h3c.1 hne0
          exact absurd ho3 hne3
        obtain ⟨ho3, hV3, hst3⟩ := h3c.2 hxzero
        refine Or.inr ⟨ho3, ?_, ?_, ?_, ?_, ?_, by rw [hV3, hv11]⟩
        · rw [hV3]
          exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect c g) hgetret1
        · rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
              (x := "ret") (y := "precompile_failed") (by decide),
              Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
              (x := "x") (y := "precompile_failed") (by decide)]
          exact hpf0
        · rw [hst3, hst2, hst1]; rfl
        · rw [hst3, hst2, hst1]; rfl
        · rw [hst3, hst2, hst1]; rfl
    · -- guard1 non-normal: x is non-canonical
      have h2c := exec_guard_iszero_lt_reject (funs := funs)
        (x := "x") (y := "r") hgetx hgetr1 h2
      have hxlt : ¬ v11.toNat < Midfall.Yul.blsR := by
        intro hxlt
        have hult : v11.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = true := by
          apply ult_of_toNat_lt
          rwa [htoNatR]
        obtain ⟨ho2, -, -⟩ := h2c.1 hult
        exact absurd ho2 hne2
      have hultf : v11.ult (BitVec.ofNat 256 Midfall.Yul.blsR) = false := by
        rw [BitVec.ult]
        exact decide_eq_false (by rwa [htoNatR])
      obtain ⟨ho2, hV2, hst2⟩ := h2c.2 hultf
      refine Or.inr ⟨ho2, ?_, ?_, ?_, ?_, ?_, by rw [hV2, hv11]⟩
      · rw [hV2]
        exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect c g) hgetret1
      · rw [hV2]
        rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect c g)
            (x := "ret") (y := "precompile_failed") (by decide),
            Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect c g)
            (x := "x") (y := "precompile_failed") (by decide)]
        exact hpf0
      · rw [hst2, hst1]; rfl
      · rw [hst2, hst1]; rfl
      · rw [hst2, hst1]; rfl
  · obtain ⟨-, -, -, -, ho1, -, -⟩ := exec_let_mload_var_inv (x := "x") (y := "mptr_start") h1
    exact absurd ho1 hne1


theorem bi_single_tail_contract (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (gas : Nat) (hgas : consts.lookup "MODEXP_GAS" = some gas)
    (succ : U256) (M : Nat → UInt8) (a s : Nat) (xv : U256)
    (hsucc : succ ≠ 0) (ha : a + 32 < 2 ^ 256) (hs : s + 224 < 2 ^ 256)
    (hx0 : 0 < xv.toNat) (hxlt : xv.toNat < Midfall.Yul.blsR)
    (hload : loadWord M a = xv) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      [ GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
          [ (match consts.lookup "MODEXP_GAS" with
              | some v => Expr.lit (Literal.number v)
              | none => Expr.var "MODEXP_GAS")
          , GenAst.ylit 5, GenAst.yvar "single_scratch", GenAst.ylit 192,
            GenAst.yvar "single_scratch", GenAst.ylit 32 ])
      , GenAst.yset "ret" (GenAst.yop EVM.Op.and
          [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
            [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]])
      , GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"])
      , GenAst.yif (GenAst.yvar "ret")
          [GenAst.yexpr (GenAst.yop EVM.Op.mstore
            [GenAst.yvar "mptr_start", GenAst.yop EVM.Op.mload [GenAst.yvar "single_scratch"]])]
      , Stmt.leave ]
      (fun V st =>
        VEnv.get V "single_scratch" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        (VEnv.get V "ret").isSome ∧ (VEnv.get V "precompile_failed").isSome ∧
        st.memory = mxMem M s xv)
      (fun V0 st V' st' o => o = .leave ∧
        ∃ ret pf, VEnv.get V' "ret" = some ret ∧
          VEnv.get V' "precompile_failed" = some pf ∧
          st'.env = st.env ∧ st'.halted = st.halted ∧
          (∀ x, (x < a ∨ a + 32 ≤ x) → (x < s ∨ s + 32 + 192 ≤ x) → st'.memory x = M x) ∧
          (pf ≠ 0 → ret = 0) ∧
          (ret ≠ 0 → pf = 0 ∧
            (loadWord M a).toNat < Midfall.Yul.blsR ∧ loadWord M a ≠ 0 ∧
            (loadWord st'.memory a).toNat < Midfall.Yul.blsR ∧
            Midfall.LoweringV3.QuotientRows.wMulmodAt (loadWord st'.memory a) (loadWord M a)
              (BitVec.ofNat 256 Midfall.Yul.blsR) = 1) ∧
          V' = VEnv.set (VEnv.set V0 "ret" ret) "precompile_failed" pf) := by
  rw [hgas]
  intro V st hpre V' st' o hrun
  change ExecStmts (D := Bridge.Dialect (permissive (callsOf product)) g) funs V st
    [GenAst.yset "ret" (GenAst.yop EVM.Op.staticcall
        [Expr.lit (Literal.number gas), GenAst.ylit 5, GenAst.yvar "single_scratch",
          GenAst.ylit 192, GenAst.yvar "single_scratch", GenAst.ylit 32]),
      GenAst.yset "ret" (GenAst.yop EVM.Op.and
        [GenAst.yvar "ret", GenAst.yop EVM.Op.eq
          [GenAst.yop EVM.Op.returndatasize [], GenAst.ylit 32]]),
      GenAst.yset "precompile_failed" (GenAst.yop EVM.Op.iszero [GenAst.yvar "ret"]),
      GenAst.yif (GenAst.yvar "ret")
        [GenAst.yexpr (GenAst.yop EVM.Op.mstore
          [GenAst.yvar "mptr_start", GenAst.yop EVM.Op.mload [GenAst.yvar "single_scratch"]])],
      Stmt.leave] V' st' o at hrun
  obtain ⟨hscratch, hmstart, hr, hret_some, hpf_some, hmem⟩ := hpre
  obtain ⟨rv0, hrv0⟩ := Option.isSome_iff_exists.mp hret_some
  obtain ⟨pfv, hpfv⟩ := Option.isSome_iff_exists.mp hpf_some
  have hbR : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have hs_toNat : (BitVec.ofNat 256 s).toNat = s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha_toNat : (BitVec.ofNat 256 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- s10 staticcall
  rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · obtain ⟨resp, -, hcall, hV1, hst1⟩ :=
      exec_assign_staticcall_var_inv (gas := gas) "single_scratch" hscratch h1
    have hst1mem : st1.memory =
        copyReturn (mxMem M s xv) s 32 resp.returndata := by
      rw [hst1, finishCall_staticcall_memory, hs_toNat, hmem]
    have henv1 : st1.env = st.env := by rw [hst1, finishCall_staticcall_env]
    have hhalt1 : st1.halted = st.halted := by
      rw [hst1, Midfall.Yul.Bridge.finishCall_staticcall_halted]
    let req : YulSemantics.EVM.CallRequest :=
      ⟨.staticcall, BitVec.ofNat 256 gas, BitVec.ofNat 256 5, 0,
        readBytes (mxMem M s xv) s 192⟩
    have hcallM : (permissive (callsOf product)).Call req st resp := by
      rw [hs_toNat, hmem] at hcall
      exact hcall
    let out : Bytes := bytesNatBE ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val 32
    have hout : modexpOutput (ByteArray.mk (readBytes (mxMem M s xv) s 192).toArray) = some out :=
      mxMem_modexpOutput M s xv hx0 hxlt
    have hpre_and : ∃ rv, VEnv.get V1 "ret" = some rv ∧
        (rv = 0 ∨ (rv = 1 ∧ st1.returndata.length = 32)) := by
      have hretV1 : VEnv.get V1 "ret" = some resp.flag := by
        rw [hV1]; exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) hrv0
      by_cases hsuccr : resp.success = true
      · have hflag1 : resp.flag = 1 := by simp [CallResponse.flag, hsuccr]
        have hcalls : (callsOf product).Call req st resp := hcallM.2 hsuccr
        have hrd := callsOf_modexp_returndata (product := product)
          (req := req) (st := st) (resp := resp) (out := out)
          rfl (modexpValidInput_of_output_some hout) hout hcalls hsuccr
        have hlen : resp.returndata.length = 32 := by
          rw [hrd, Array.length_toList, ByteArray.size_data]
          exact Midfall.Assumptions.bytesNatBE_size _ 32
        have hlen1 : st1.returndata.length = 32 := by rw [hst1]; exact hlen
        exact ⟨1, by rw [hretV1, hflag1], Or.inr ⟨rfl, hlen1⟩⟩
      · have hflag0 : resp.flag = 0 := by simp [CallResponse.flag, hsuccr]
        exact ⟨0, by rw [hretV1, hflag0], Or.inl rfl⟩
    have hpfV1 : VEnv.get V1 "precompile_failed" = some pfv := by
      rw [hV1]
      exact (Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
        (x := "ret") (y := "precompile_failed") (by decide)).trans hpfv
    -- s11 ret := and(ret, eq(returndatasize(), 32))
    rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · have hretV1 : VEnv.get V1 "ret" = some resp.flag := by
        rw [hV1]; exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) hrv0
      have h2c := ret_and_eq32_stmt (c := permissive (callsOf product)) (g := g) funs
        (V := V1) (st := st1) hpre_and V2 st2 .normal h2
      obtain ⟨-, rv2, hretV1', hV2, hst2⟩ := h2c
      by_cases hsuccr : resp.success = true
      · -- SUCCESS
        have hflag1 : resp.flag = 1 := by simp [CallResponse.flag, hsuccr]
        have hrv2 : rv2 = 1 := by
          rw [hretV1] at hretV1'
          rw [hflag1] at hretV1'
          exact (Option.some.inj hretV1').symm
        subst hrv2
        have hretV2 : VEnv.get V2 "ret" = some 1 := by
          rw [hV2]; exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) hretV1'
        rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest2 with
          ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
        · have h3c := exec_assign_iszero_one (c := permissive (callsOf product)) (g := g)
            (V := V2) (st := st2) hretV2 h3
          obtain ⟨-, hV3, hst3⟩ := h3c
          have hretV3 : VEnv.get V3 "ret" = some (1 : U256) := by
            rw [hV3]
            exact (Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g) (x := "precompile_failed") (y := "ret")
              (by decide)).trans hretV2
          have hpfV3 : VEnv.get V3 "precompile_failed" = some (0 : U256) := by
            rw [hV3]
            exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) (by
              rw [hV2]
              exact (Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "ret") (y := "precompile_failed") (by decide)).trans hpfV1)
          rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest3 with
            ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
          · -- guard if ret true, body mstore
            have hbody := (exec_guard_var_body (x := "ret") (rv := 1) hretV3 h4).1 (by decide : (1 : U256) ≠ 0)
            obtain ⟨Vb, stb, hb, hV4, hst4⟩ := exec_block_inv (funs := funs) hbody
            rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hb with
              ⟨Vc, stc, hm, hnil⟩ | ⟨hm, hne_m⟩
            · cases hnil
              obtain ⟨xvA, yvA, hxva, hyva, -, hVc, hmemc, henvc, hhaltc⟩ :=
                exec_mstore_var_mload_mem (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
                  [Stmt.exprStmt (Expr.builtin Op.mstore
                    [Expr.var "mptr_start", Expr.builtin Op.mload [Expr.var "single_scratch"]])] :: funs) hm
              subst hVc
              have hgpm : Vb.get "mptr_start" = some (BitVec.ofNat 256 a) := by
                rw [hV3, hV2, hV1]
                rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "precompile_failed") (y := "mptr_start") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "ret") (y := "mptr_start") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "ret") (y := "mptr_start") (by decide)]
                exact hmstart
              have hgps : Vb.get "single_scratch" = some (BitVec.ofNat 256 s) := by
                rw [hV3, hV2, hV1]
                rw [Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "precompile_failed") (y := "single_scratch") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "ret") (y := "single_scratch") (by decide),
                    Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                      (x := "ret") (y := "single_scratch") (by decide)]
                exact hscratch
              have hxvA : xvA = BitVec.ofNat 256 a := by
                rw [hgpm] at hxva
                exact (Option.some.inj hxva).symm
              have hyvA : yvA = BitVec.ofNat 256 s := by
                rw [hgps] at hyva
                exact (Option.some.inj hyva).symm
              subst hxvA hyvA
              have hV4' : V4 = Vb := by
                rw [hV4]
                simp [restore]
              subst hV4'
              subst hst4
              -- s14 leave
              rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest4 with
                ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
              · cases h5
              · cases h5
                have hcalls : (callsOf product).Call req st resp := hcallM.2 hsuccr
                have hrd := callsOf_modexp_returndata (product := product)
                  (req := req) (st := st) (resp := resp) (out := out)
                  rfl (modexpValidInput_of_output_some hout) hout hcalls hsuccr
                have hmemc' : st'.memory =
                    storeWord st3.memory a (loadWord st3.memory (BitVec.ofNat 256 s).toNat) := by
                  rw [hmemc, ha_toNat]
                have hloadS : loadWord st'.memory a =
                    BitVec.ofNat 256 ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val := by
                  rw [hmemc', Midfall.Yul.Word.loadWord_storeWord_same, hst3, hst2, hst1mem,
                    hs_toNat, hrd]
                  exact loadWord_copyReturn_bytesNatBE (mem := mxMem M s xv) (p := s) _ (zmod_inv_val_lt xv)
                refine ⟨rfl, 1, 0, hretV3, hpfV3, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · rw [henvc, hst3, hst2, henv1]
                · rw [hhaltc, hst3, hst2, hhalt1]
                · -- outside
                  intro x hxa hxs
                  rw [hmemc]
                  rw [Midfall.LoweringV3.BatchInvert.storeWord_outside _ _ _ _ (by omega)]
                  rw [hst3, hst2, hst1mem]
                  rw [copyReturn_outside' _ _ _ _ _ (by
                    have hmin := Nat.min_le_left 32 resp.returndata.length
                    omega)]
                  exact mxMem_outside M s xv x (by omega)
                · -- pf≠0 → ret=0
                  intro hpfne
                  exact absurd rfl hpfne
                · intro hretne
                  have hInvB : ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val < 2 ^ 256 := by
                    have h := ZMod.val_lt ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹)
                    omega
                  have hInvToNat :
                      (BitVec.ofNat 256 ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val).toNat =
                        ((xv.toNat : ZMod Midfall.Yul.blsR)⁻¹).val := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hInvB]
                  have hxv0 : xv ≠ 0 := by
                    intro h0
                    rw [h0] at hx0
                    simp at hx0
                  rw [hload, hloadS, hInvToNat]
                  exact ⟨rfl, hxlt, hxv0, ZMod.val_lt _,
                    wMulmodAt_zmod_inv xv (Nat.ne_of_gt hx0) hxlt⟩
                · rw [hV3, hV2, hV1, hflag1, Midfall.LoweringV3.LagrangeRows.venv_set_set (D := Bridge.Dialect (permissive (callsOf product)) g)]
            · cases hm with
              | exprStmt _ => exact absurd rfl hne_m
          · have hbody := (exec_guard_var_body (x := "ret") (rv := 1) hretV3 h4).1
              (by decide : (1 : U256) ≠ 0)
            obtain ⟨Vb, stb, hb, -, -⟩ := exec_block_inv (funs := funs) hbody
            rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hb with
              ⟨Vc, stc, hm, hnil⟩ | ⟨hm, hne_m⟩
            · cases hnil
              exact absurd rfl hne4
            · cases hm with
              | exprStmt _ => exact absurd rfl hne_m
              | exprStmtHalt he =>
                  exact (by
                    cases he with
                    | builtinHalt hargs hbi =>
                        simp only [builtinWithExternal, stepOp] at hbi
                        split at hbi <;> simp at hbi
                    | builtinArgsHalt hargs =>
                        cases hargs with
                        | argsRestHalt h' =>
                            cases h' with
                            | argsRestHalt h'' => cases h''
                            | argsHeadHalt _ hval => exact (eval_mload_var_halt_false hval).elim
                        | argsHeadHalt _ hx =>
                            exact (Midfall.LoweringV2.Blocks.VkLoading.vkVar_ne_halts hx).elim)
        · obtain ⟨ho3, -, -⟩ := exec_assign_iszero_one (c := permissive (callsOf product)) (g := g)
            (V := V2) (st := st2) hretV2 h3
          exact absurd ho3 hne3
      · -- FAILURE
        have hflag0 : resp.flag = 0 := by simp [CallResponse.flag, hsuccr]
        have hrv2 : rv2 = 0 := by
          rw [hretV1] at hretV1'
          rw [hflag0] at hretV1'
          exact (Option.some.inj hretV1').symm
        subst hrv2
        have hretV2 : VEnv.get V2 "ret" = some 0 := by
          rw [hV2]; exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) hretV1'
        rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest2 with
          ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
        · have h3c := exec_assign_iszero_zero (c := permissive (callsOf product)) (g := g)
            (V := V2) (st := st2) hretV2 h3
          obtain ⟨-, hV3, hst3⟩ := h3c
          have hretV3 : VEnv.get V3 "ret" = some (0 : U256) := by
            rw [hV3]
            exact (Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g) (x := "precompile_failed") (y := "ret")
              (by decide)).trans hretV2
          have hpfV3 : VEnv.get V3 "precompile_failed" = some (1 : U256) := by
            rw [hV3]
            exact Midfall.LoweringV3.LagrangeRows.venv_get_set_same (D := Bridge.Dialect (permissive (callsOf product)) g) (by
              rw [hV2]
              exact (Midfall.LoweringV3.LagrangeRows.venv_get_set_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
                (x := "ret") (y := "precompile_failed") (by decide)).trans hpfV1)
          rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest3 with
            ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
          · obtain ⟨-, hV4, hst4⟩ := (exec_guard_var_body (x := "ret") (rv := 0) hretV3 h4).2 rfl
            subst hV4 hst4
            rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest4 with
              ⟨V5, st5, h5, hrest5⟩ | ⟨h5, hne5⟩
            · cases h5
            · cases h5
              refine ⟨rfl, 0, 1, hretV3, hpfV3, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hst3, hst2, henv1]
              · rw [hst3, hst2, hhalt1]
              · intro x hxa hxs
                rw [hst3, hst2, hst1mem]
                rw [copyReturn_outside' _ _ _ _ _ (by
                  have hmin := Nat.min_le_left 32 resp.returndata.length
                  omega)]
                exact mxMem_outside M s xv x (by omega)
              · intro hpfne
                rfl
              · intro hretne
                exact absurd rfl hretne
              · rw [hV3, hV2, hV1, hflag0, Midfall.LoweringV3.LagrangeRows.venv_set_set (D := Bridge.Dialect (permissive (callsOf product)) g)]
          · obtain ⟨ho4, -, -⟩ := (exec_guard_var_body (x := "ret") (rv := 0) hretV3 h4).2 rfl
            exact absurd ho4 hne4
        · obtain ⟨ho3, -, -⟩ := exec_assign_iszero_zero (c := permissive (callsOf product)) (g := g)
            (V := V2) (st := st2) hretV2 h3
          exact absurd ho3 hne3
    · obtain ⟨ho2, -, -⟩ := ret_and_eq32_stmt (c := permissive (callsOf product)) (g := g) funs
        (V := V1) (st := st1) hpre_and V' st' o h2
      exact absurd ho2 hne2
  · obtain ⟨-, ho1, -⟩ :=
      exec_assign_staticcall_var_inv (gas := gas) "single_scratch" hscratch h1
    exact absurd ho1 hne1


theorem bi_single_contract (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (gas : Nat) (hgas : consts.lookup "MODEXP_GAS" = some gas)
    (succ : U256) (a s : Nat) (hsucc : succ ≠ 0)
    (ha : a + 32 < 2 ^ 256) (hs : s + 224 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (biSingleArm consts)
      (fun V st =>
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "scratch_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        VEnv.get V "ret" = some succ ∧
        VEnv.get V "precompile_failed" = some 0)
      (fun V0 st V' st' o => o = .leave ∧
        (BatchInvertPost (c := permissive (callsOf product)) (g := g) st succ a (a + 32) s
          (BitVec.ofNat 256 Midfall.Yul.blsR) V' st' ∧
        ((V' = VEnv.set (("x", loadWord st.memory a) :: V0) "ret" 0) ∨
          ∃ ret pf, VEnv.get V' "ret" = some ret ∧
            VEnv.get V' "precompile_failed" = some pf ∧
            V' = VEnv.set (VEnv.set
              (("single_scratch", BitVec.ofNat 256 s) :: ("x", loadWord st.memory a) :: V0)
              "ret" ret) "precompile_failed" pf))) := by
  rw [biSingleArm_eq]
  intro V st hpre V' st' o hrun
  rcases Step.stmts_append_inv hrun with ⟨V1, st1, hhead, htail⟩ | ⟨hhead, hne⟩
  · have hh := bi_single_head_contract (c := permissive (callsOf product)) (g := g) funs
      succ a s ha V st hpre V1 st1 .normal hhead
    rcases hh with
      ⟨-, hx, hsc, hxlt, hx0, hms, hr, hret1, hpf1, hmem1, henv1, hhalt1, hshape1⟩ |
      ⟨ho, hret0, hpf0, hmem0, henv0, hhalt0, hshape0⟩
    · rcases Step.stmts_append_inv htail with ⟨V2, st2, hframe, htail2⟩ | ⟨hframe, hne2⟩
      · have hxpos : 0 < (loadWord st.memory a).toNat := by
          apply Nat.pos_of_ne_zero
          intro hz
          apply hx0
          apply BitVec.eq_of_toNat_eq
          rw [hz]
          rfl
        have hf := modexpFrameStores_single_mxMem (c := permissive (callsOf product)) (g := g)
          funs (BitVec.ofNat 256 s) (loadWord st.memory a)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s < 2 ^ 256)]; omega)
          V1 st1 ⟨hsc, hx, hr⟩ V2 st2 .normal hframe
        obtain ⟨-, hV2, hmem2, henv2, hhalt2⟩ := hf
        rw [← hV2] at hsc hms hr hret1 hpf1
        have hs_toNat : (BitVec.ofNat 256 s).toNat = s := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s < 2 ^ 256)]
        have htailc := bi_single_tail_contract (consts := consts) (product := product) (g := g)
          funs gas hgas succ (st.memory) a s (loadWord st.memory a) hsucc ha hs hxpos hxlt rfl
          V2 st2 ⟨hsc, hms, hr, (Option.isSome_iff_exists.mpr ⟨succ, hret1⟩),
            (Option.isSome_iff_exists.mpr ⟨0, hpf1⟩), by rw [hmem2, hmem1, hs_toNat]⟩
          V' st' o htail2
        obtain ⟨ho_tail, ret, pf, hretT, hpfT, henvT, hhaltT, houtT, hpfret, hsuccT, hshapeT⟩ := htailc
        refine ⟨ho_tail, ⟨ret, pf, hretT, hpfT, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨ret, pf, hretT, hpfT, by rw [hshapeT, hV2, hshape1]⟩⟩
        · rw [henvT, henv2, henv1]
        · rw [hhaltT, hhalt2, hhalt1]
        · intro x hxa hxs
          rw [show a + 32 - a = 32 from by omega] at hxs
          exact houtT x hxa hxs
        · intro hs0
          exact absurd hs0 hsucc
        · exact hpfret
        · intro hretne
          obtain ⟨hpf0', hcanon, hnonzero, hinvlt, hinvw⟩ := hsuccT hretne
          refine ⟨hpf0', ?_⟩
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          exact ⟨hcanon, hnonzero, hinvlt, hinvw⟩
      · obtain ⟨ho, -, -⟩ := modexpFrameStores_single_mxMem (c := permissive (callsOf product)) (g := g)
          funs (BitVec.ofNat 256 s) (loadWord st.memory a)
          (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s < 2 ^ 256)]; omega)
          V1 st1 ⟨hsc, hx, hr⟩ V' st' o hframe
        exact absurd ho hne2
    · exact absurd ho (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)

  · have hh := bi_single_head_contract (c := permissive (callsOf product)) (g := g) funs
      succ a s ha V st hpre V' st' o hhead
    rcases hh with
      ⟨hnormal, hx, hsc, hxlt, hx0, hms, hr, hret1, hpf1, hmem1, henv1, hhalt1, -⟩ |
      ⟨ho, hret0, hpf0, hmem0, henv0, hhalt0, hshape0⟩
    · exact absurd hnormal hne
    · exact ⟨ho, BatchInvertPost_zero (c := permissive (callsOf product)) (g := g)
        succ (BitVec.ofNat 256 Midfall.Yul.blsR) a (a + 32) s hsucc hret0 (Option.isSome_iff_exists.mpr ⟨0, hpf0⟩)
        henv0 hhalt0 (by intro x _ _; rw [hmem0]), Or.inl hshape0⟩


theorem bi_prelude_single (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (gas : Nat) (hgas : consts.lookup "MODEXP_GAS" = some gas)
    (succ : U256) (a s : Nat) (hsucc : succ ≠ 0)
    (ha : a + 32 < 2 ^ 256) (hs : s + 224 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (seg (helperBody consts Midfall.Lowering.GenAst.emitBatchInvertAt) 2 8)
      (fun V st =>
        VEnv.get V "mptr_start" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V "scratch_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) ∧
        VEnv.get V "ret" = some succ ∧
        VEnv.get V "precompile_failed" = some 0)
      (fun _ st V' st' o => o = .leave ∧
        BatchInvertPost (c := permissive (callsOf product)) (g := g) st succ a (a + 32) s
          (BitVec.ofNat 256 Midfall.Yul.blsR) V' st') := by
  rw [bi_prelude_single_form]
  intro V st hpre V' st' o hrun
  obtain ⟨hmstart, hend, hscratch, hr, hret, hpf0⟩ := hpre
  have hbR : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have htoNatR : (BitVec.ofNat 256 Midfall.Yul.blsR).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR]
  have hae : a ≤ a + 32 := by omega
  have he32 : a + 32 < 2 ^ 256 := ha
  have hsub : (BitVec.ofNat 256 (a + 32) - BitVec.ofNat 256 a : U256) =
      BitVec.ofNat 256 32 := by
    rw [ofNat_sub_of_le a (a + 32) hae he32]
    rw [show a + 32 - a = 32 by omega]
  -- s2
  rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrun with
    ⟨V1, st1, h1, hrest1⟩ | ⟨h1, hne1⟩
  · have h1c := exec_guard_ret0_lt_vars_false (x := "mptr_end") (y := "mptr_start")
      hend hmstart (ofNat_ult_ofNat_false a (a + 32) hae he32) h1
    obtain ⟨-, hV1, hst1⟩ := h1c
    subst hV1
    -- s3
    rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest1 with
      ⟨V2, st2, h2, hrest2⟩ | ⟨h2, hne2⟩
    · obtain ⟨yv, zv, hyv, hzv, -, hV2, hst2⟩ :=
        exec_let_sub_vars_inv (x := "count_bytes") (y := "mptr_end") (z := "mptr_start") h2
      rw [hend] at hyv
      rw [hmstart] at hzv
      injection hyv with hy
      injection hzv with hz
      subst hy hz
      rw [hsub] at hV2
      subst hV2
      have hcount : VEnv.get (("count_bytes", BitVec.ofNat 256 32) :: V1) "count_bytes" =
          some (BitVec.ofNat 256 32) := rfl
      -- s4
      rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest2 with
        ⟨V3, st3, h3, hrest3⟩ | ⟨h3, hne3⟩
      · have h3c := (exec_guard_iszero_var (x := "count_bytes") hcount h3).1
          (ofNat_ne_zero_of_pos (by norm_num) (by norm_num : 32 < 2 ^ 256))
        obtain ⟨-, hV3, hst3⟩ := h3c
        have hs1 : VEnv.get V3 "mptr_start" = some (BitVec.ofNat 256 a) := by
          rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
            (x := "count_bytes") (y := "mptr_start") (by decide)]
          exact hmstart
        have hs2 : VEnv.get V3 "scratch_mptr" = some (BitVec.ofNat 256 s) := by
          rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
            (x := "count_bytes") (y := "scratch_mptr") (by decide)]
          exact hscratch
        have hs3 : VEnv.get V3 "r" = some (BitVec.ofNat 256 Midfall.Yul.blsR) := by
          rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
            (x := "count_bytes") (y := "r") (by decide)]
          exact hr
        have hs4 : VEnv.get V3 "ret" = some succ := by
          rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
            (x := "count_bytes") (y := "ret") (by decide)]
          exact hret
        have hs5 : VEnv.get V3 "precompile_failed" = some 0 := by
          rw [hV3]
          rw [Midfall.LoweringV3.LagrangeRows.venv_get_cons_ne (D := Bridge.Dialect (permissive (callsOf product)) g)
            (x := "count_bytes") (y := "precompile_failed") (by decide)]
          exact hpf0
        -- s5 true branch
        rcases Step.stmts_cons_inv (D := Bridge.Dialect (permissive (callsOf product)) g) hrest3 with
          ⟨V4, st4, h4, hrest4⟩ | ⟨h4, hne4⟩
        · -- the if statement is normal: impossible because the body leaves
          cases h4 with
          | ifTrue hc hnz hbody =>
              obtain ⟨-, -, -, hstc⟩ := eval_eq_var_lit_inv (x := "count_bytes") (k := 32) hc
              rw [hstc] at hbody
              obtain ⟨Vb, stb, hb, -, -⟩ := exec_block_inv (funs := funs) hbody
              have hsc := bi_single_contract (consts := consts) (product := product) (g := g)
                (hoist (Bridge.Dialect (permissive (callsOf product)) g) (biSingleArm consts) :: funs)
                gas hgas succ a s hsucc ha hs V3 st3 ⟨hs1, hs2, hs3, hs4, hs5⟩
                Vb stb .normal hb
              exact absurd hsc.1 (by decide : (Outcome.normal : Outcome) ≠ Outcome.leave)
          | ifFalse hc hz =>
              obtain ⟨xv, hxv, hcv, -⟩ := eval_eq_var_lit_inv (x := "count_bytes") (k := 32) hc
              rw [hV3, hcount] at hxv
              injection hxv with hxv'
              subst hxv'
              rw [hcv] at hz
              change (1 : U256) = (0 : U256) at hz
              exact absurd hz (by decide)
        · cases h4 with
          | ifTrue hc hnz hbody =>
              obtain ⟨-, -, -, hstc⟩ := eval_eq_var_lit_inv (x := "count_bytes") (k := 32) hc
              rw [hstc] at hbody
              obtain ⟨Vb, stb, hb, hVb, hstb⟩ := exec_block_inv (funs := funs) hbody
              -- pre for the single arm
              have hsc := bi_single_contract (consts := consts) (product := product) (g := g)
                (hoist (Bridge.Dialect (permissive (callsOf product)) g) (biSingleArm consts) :: funs)
                gas hgas succ a s hsucc ha hs V3 st3 ⟨hs1, hs2, hs3, hs4, hs5⟩
                Vb stb o hb
              have ho := hsc.1
              have hVbBIP : BatchInvertPost (c := permissive (callsOf product)) (g := g)
                  st3 succ a (a + 32) s (BitVec.ofNat 256 Midfall.Yul.blsR) Vb stb := hsc.2.1
              have hshape := hsc.2.2
              -- transport V' = restore V3 Vb to an explicit env and BIP
              have hst3eq : st3 = st := by rw [hst3, hst2, hst1]
              rw [hst3eq] at hshape
              -- functions for get congruence over the restored env
              have htransfer : BatchInvertPost (c := permissive (callsOf product)) (g := g)
                  st3 succ a (a + 32) s (BitVec.ofNat 256 Midfall.Yul.blsR) V' stb := by
                obtain ⟨retB, pfB, hretB, hpfB, henvB, hhaltB, houtB, hsuccB, hpfB0, hretB0⟩ := hVbBIP
                rcases hshape with hshape0 | ⟨retS, pfS, hretS, hpfS, hshapeS⟩
                · -- reject: Vb = ("x",..) :: set V3 ret 0
                  have hVb_eq : Vb = ("x", loadWord st.memory a) ::
                      VEnv.set V3 "ret" 0 := by
                    rw [hshape0]
                    simp [VEnv.set]
                  have hV'_eq : V' = VEnv.set V3 "ret" 0 := by
                    rw [hVb, hVb_eq]
                    rw [Midfall.LoweringV3.LagrangeRows.restore_cons_length
                      (V := V3) (W := VEnv.set V3 "ret" 0) (y := "x")
                      (b := loadWord st.memory a) (by rw [Midfall.LoweringV3.LagrangeRows.venv_set_length (D := Bridge.Dialect (permissive (callsOf product)) g) V3 "ret" 0])]
                  have hgetret : VEnv.get Vb "ret" = VEnv.get V' "ret" := by
                    rw [hVb_eq, hV'_eq]
                    simp [VEnv.get, List.find?]
                  have hgetpf : VEnv.get Vb "precompile_failed" = VEnv.get V' "precompile_failed" := by
                    rw [hVb_eq, hV'_eq]
                    simp [VEnv.get, List.find?]
                  refine ⟨retB, pfB, ?_, ?_, henvB, hhaltB, houtB, hsuccB, hpfB0, hretB0⟩
                  · rw [← hgetret]; exact hretB
                  · rw [← hgetpf]; exact hpfB
                · -- normal: Vb = ("single_scratch",..) :: ("x",..) :: set (set V3 ret) pf
                  have hVb_eq : Vb = ("single_scratch", BitVec.ofNat 256 s) ::
                      ("x", loadWord st.memory a) ::
                        VEnv.set (VEnv.set V3 "ret" retS) "precompile_failed" pfS := by
                    rw [hshapeS]
                    simp [VEnv.set]
                  have hV'_eq : V' = VEnv.set (VEnv.set V3 "ret" retS) "precompile_failed" pfS := by
                    rw [hVb, hVb_eq]
                    rw [Midfall.LoweringV3.LagrangeRows.restore_two_cons_length
                      (V := V3) (W := VEnv.set (VEnv.set V3 "ret" retS) "precompile_failed" pfS)
                      (y := "single_scratch") (z := "x")
                      (b := BitVec.ofNat 256 s) (c := loadWord st.memory a)
                      (by rw [Midfall.LoweringV3.LagrangeRows.venv_set_length (D := Bridge.Dialect (permissive (callsOf product)) g) (VEnv.set V3 "ret" retS) "precompile_failed" pfS,
                        Midfall.LoweringV3.LagrangeRows.venv_set_length (D := Bridge.Dialect (permissive (callsOf product)) g) V3 "ret" retS])]
                  have hgetret : VEnv.get Vb "ret" = VEnv.get V' "ret" := by
                    rw [hVb_eq, hV'_eq]
                    simp [VEnv.get, List.find?]
                  have hgetpf : VEnv.get Vb "precompile_failed" = VEnv.get V' "precompile_failed" := by
                    rw [hVb_eq, hV'_eq]
                    simp [VEnv.get, List.find?]
                  refine ⟨retB, pfB, ?_, ?_, henvB, hhaltB, houtB, hsuccB, hpfB0, hretB0⟩
                  · rw [← hgetret]; exact hretB
                  · rw [← hgetpf]; exact hpfB
              refine ⟨ho, ?_⟩
              rw [hstb]
              rw [hst3eq] at htransfer
              exact htransfer
          | ifFalse hc hz =>
              obtain ⟨xv, hxv, hcv, -⟩ := eval_eq_var_lit_inv (x := "count_bytes") (k := 32) hc
              rw [hV3, hcount] at hxv
              injection hxv with hxv'
              subst hxv'
              rw [hcv] at hz
              change (1 : U256) = (0 : U256) at hz
              exact absurd hz (by decide)
          | ifHalt hc => exact (eval_eq_var_lit_no_halt (x := "count_bytes") (k := 32) hc).elim
      · obtain ⟨ho3, -, -⟩ := (exec_guard_iszero_var (x := "count_bytes") hcount h3).1
          (ofNat_ne_zero_of_pos (by norm_num) (by norm_num : 32 < 2 ^ 256))
        exact absurd ho3 hne3
    · obtain ⟨-, -, -, -, ho2, -, -⟩ :=
        exec_let_sub_vars_inv (x := "count_bytes") (y := "mptr_end") (z := "mptr_start") h2
      exact absurd ho2 hne2
  · obtain ⟨ho1, -, -⟩ := exec_guard_ret0_lt_vars_false (x := "mptr_end") (y := "mptr_start")
      hend hmstart (ofNat_ult_ofNat_false a (a + 32) hae he32) h1
    exact absurd ho1 hne1


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
#assert_axioms rest_success [propext, Classical.choice, Quot.sound]
#assert_axioms rest_failure [propext, Classical.choice, Quot.sound]
#assert_axioms rest_success_run [propext, Classical.choice, Quot.sound]
#assert_axioms rest_failure_run [propext, Classical.choice, Quot.sound]
#assert_axioms walk_success_build [propext, Classical.choice, Quot.sound]
#assert_axioms walk_failure_build [propext, Classical.choice, Quot.sound]
#assert_axioms head_ret [propext, Classical.choice, Quot.sound]
#assert_axioms head_gp_mptr [propext, Classical.choice, Quot.sound]
#assert_axioms head_mptr_start [propext, Classical.choice, Quot.sound]
#assert_axioms head_r [propext, Classical.choice, Quot.sound]
#assert_axioms head_gp [propext, Classical.choice, Quot.sound]
#assert_axioms head_pf_some [propext, Classical.choice, Quot.sound]
#assert_axioms walk_success_rest [propext, Classical.choice, Quot.sound]
#assert_axioms walk_failure_rest [propext, Classical.choice, Quot.sound]
#assert_axioms bi_staticcall_walk [propext, Classical.choice, Quot.sound]
#assert_axioms bi_prelude_main [propext, Classical.choice, Quot.sound]
#assert_axioms wMulmodAt_zmod_inv [propext, Classical.choice, Quot.sound]
#assert_axioms fwdProd_zmod_inv [propext, Classical.choice, Quot.sound]
#assert_axioms ofNat_sub_two_blsR [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_stores [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_head_form [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_head [propext, Classical.choice, Quot.sound]
#assert_axioms bi_bridge_contract [propext, Classical.choice, Quot.sound]
#assert_axioms exec_guard_var_body [propext, Classical.choice, Quot.sound]
#assert_axioms mxMem_outside [propext, Classical.choice, Quot.sound]
#assert_axioms copyReturn_outside' [propext, Classical.choice, Quot.sound]
#assert_axioms eval_staticcall_args_var [propext, Classical.choice, Quot.sound]
#assert_axioms exec_assign_staticcall_var_inv [propext, Classical.choice, Quot.sound]
#assert_axioms exec_mstore_var_mload_mem [propext, Classical.choice, Quot.sound]
#assert_axioms modexpFrameStores_single_contract [propext, Classical.choice, Quot.sound]
#assert_axioms modexpFrameStores_single_mxMem [propext, Classical.choice, Quot.sound]
#assert_axioms bi_single_head_contract [propext, Classical.choice, Quot.sound]
#assert_axioms bi_single_tail_contract [propext, Classical.choice, Quot.sound]
#assert_axioms bi_single_contract [propext, Classical.choice, Quot.sound]
#assert_axioms bi_prelude_single [propext, Classical.choice, Quot.sound]
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

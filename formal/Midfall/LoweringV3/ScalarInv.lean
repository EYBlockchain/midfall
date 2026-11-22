/-
  Midfall.LoweringV3.ScalarInv

  A9 (ROW.PCS, block 4 helper) - THE MEMORY-LEVEL `scalar_inv` FRAME.

  `GenAst.emitScalarInvAt` writes six 32-byte words at `p, p+32, …, p+160`
  (`modexpFrameStores`, GenAst.lean:408-417): the EIP-198 lengths `32,32,32`, the base `x`,
  the exponent `FR_MODULUS - 2`, and the modulus `FR_MODULUS`. This file proves that the six
  stores read back as exactly `modexpInvFrame x` (`Yul/Externals.lean:560`), i.e. the frame
  `modexpInv_correct` (`Assumptions/Eip2537.lean:825`) parses. It lands NO summary yet and
  wires no row: the `fail` effect, the guard arms, the honest staticcall and the read-back
  are the next pieces.

  The bridge uses the already-landed 32-byte facts `readBytes_storeWord_32`,
  `bytesToNatBE_readBytes_32`, `readBytes_append` and `readBytes_storeWord_outside`
  (`PcsRows.lean`). No fixture, no native_decide, no extra hypothesis.
-/
import Midfall.LoweringV3.PcsRows
import Midfall.LoweringV2.Blocks.TraceReturn
set_option autoImplicit false

namespace Midfall.LoweringV3.ScalarInv

open Midfall Midfall.Lowering Midfall.Generator Midfall.LoweringV3.PcsRows
open Midfall.LoweringV2 Midfall.LoweringV2.Blocks.TraceReturn
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge

variable {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. A fold of stores at `p, p+32, …` -/

/-- Store a list of words at `p + 32*i`, left to right. -/
def storeWords (mem : Nat → UInt8) (p : Nat) : List U256 → Nat → (Nat → UInt8)
  | [], _ => mem
  | v :: vs, i => storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1)

/-- All stores of `storeWords … vs i` are at addresses `≥ p + 32*i`, so a read whose window
    ends before `p + 32*i` is blind to them. -/
theorem readBytes_storeWords_outside (mem : Nat → UInt8) (p : Nat) :
    ∀ (vs : List U256) (i q n : Nat), q + n ≤ p + 32 * i →
      readBytes (storeWords mem p vs i) q n = readBytes mem q n
  | [], i, q, n, _ => rfl
  | v :: vs, i, q, n, h => by
      change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1)) q n =
        readBytes mem q n
      rw [readBytes_storeWords_outside (storeWord mem (p + 32 * i) v) p vs (i + 1) q n
        (by omega)]
      rw [readBytes_storeWord_outside (mem := mem) (q := p + 32 * i) (v := v) (p := q) (n := n)
        (by omega)]

/-- **A BLOCK OF THE TABLE**: after `storeWords`, the 32 bytes at `p + 32*(i+k)` are the
    `bytesNatBE` encoding of the `k`-th word. -/
theorem readBytes_storeWords_block (mem : Nat → UInt8) (p : Nat) :
    ∀ (vs : List U256) (i k : Nat), k < vs.length →
      readBytes (storeWords mem p vs i) (p + 32 * (i + k)) 32 =
        (bytesNatBE (vs.getD k 0).toNat 32).data.toList
  | [], i, k, hk => absurd hk (Nat.not_lt_zero k)
  | v :: vs, i, k, hk => by
      cases k with
      | zero =>
          change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1))
            (p + 32 * i) 32 = (bytesNatBE v.toNat 32).data.toList
          rw [readBytes_storeWords_outside (storeWord mem (p + 32 * i) v) p vs (i + 1)
            (p + 32 * i) 32 (by omega)]
          rw [readBytes_storeWord_32]
      | succ k =>
          have hk' : k < vs.length := by simpa using hk
          change readBytes (storeWords (storeWord mem (p + 32 * i) v) p vs (i + 1))
            (p + 32 * (i + (k + 1))) 32 = (bytesNatBE (vs.getD k 0).toNat 32).data.toList
          rw [show p + 32 * (i + (k + 1)) = p + 32 * ((i + 1) + k) by omega]
          exact readBytes_storeWords_block (storeWord mem (p + 32 * i) v) p vs (i + 1) k hk'

/-! ## 2. The six words of `scalar_inv` -/

/-- The six memory words `scalar_inv` writes. -/
def mxMem (mem : Nat → UInt8) (p : Nat) (x : U256) : Nat → UInt8 :=
  storeWord (storeWord (storeWord (storeWord (storeWord (storeWord mem p 32)
    (p + 32) 32) (p + 64) 32) (p + 96) x) (p + 128)
    (BitVec.ofNat 256 (Midfall.Yul.blsR - 2))) (p + 160) (BitVec.ofNat 256 Midfall.Yul.blsR)

/-- The same six words as a list, for the block lemma. -/
def mxWords (x : U256) : List U256 :=
  [32, 32, 32, x, BitVec.ofNat 256 (Midfall.Yul.blsR - 2), BitVec.ofNat 256 Midfall.Yul.blsR]

theorem mxMem_eq_storeWords (mem : Nat → UInt8) (p : Nat) (x : U256) :
    mxMem mem p x = storeWords mem p (mxWords x) 0 := rfl

/-- **THE SIX-BLOCK READ**: the 192 bytes read back are the six `bytesNatBE` blocks. -/
theorem mxMem_read192 (mem : Nat → UInt8) (p : Nat) (x : U256) :
    readBytes (mxMem mem p x) p 192 =
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE 32 32).data.toList ++
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE x.toNat 32).data.toList ++
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList ++
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
  rw [mxMem_eq_storeWords]
  have h0 : readBytes (storeWords mem p (mxWords x) 0) p 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 0 (by simp [mxWords])
  have h1 : readBytes (storeWords mem p (mxWords x) 0) (p + 32) 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 1 (by simp [mxWords])
  have h2 : readBytes (storeWords mem p (mxWords x) 0) (p + 64) 32 =
      (bytesNatBE 32 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 2 (by simp [mxWords])
  have h3 : readBytes (storeWords mem p (mxWords x) 0) (p + 96) 32 =
      (bytesNatBE x.toNat 32).data.toList := by
    simpa [mxWords] using readBytes_storeWords_block mem p (mxWords x) 0 3 (by simp [mxWords])
  have hbR : Midfall.Yul.blsR < 2 ^ 256 := by decide
  have hbR2 : Midfall.Yul.blsR - 2 < 2 ^ 256 := by omega
  have htoR2 : (BitVec.ofNat 256 (Midfall.Yul.blsR - 2)).toNat = Midfall.Yul.blsR - 2 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR2]
  have htoR : (BitVec.ofNat 256 Midfall.Yul.blsR).toNat = Midfall.Yul.blsR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbR]
  have h4 : readBytes (storeWords mem p (mxWords x) 0) (p + 128) 32 =
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList := by
    simpa [mxWords, htoR2] using
      readBytes_storeWords_block mem p (mxWords x) 0 4 (by simp [mxWords])
  have h5 : readBytes (storeWords mem p (mxWords x) 0) (p + 160) 32 =
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
    simpa [mxWords, htoR] using
      readBytes_storeWords_block mem p (mxWords x) 0 5 (by simp [mxWords])
  rw [show 192 = 32 + 160 by omega, readBytes_append]
  rw [show 160 = 32 + 128 by omega, readBytes_append]
  rw [show 128 = 32 + 96 by omega, readBytes_append]
  rw [show 96 = 32 + 64 by omega, readBytes_append]
  rw [show 64 = 32 + 32 by omega, readBytes_append]
  rw [h0, h1, h2, h3, h4, h5]
  simp [List.append_assoc]

/-- **THE FRAME DATA**: `modexpInvFrame x` is the same six blocks. -/
theorem modexpInvFrame_data (x : Nat) :
    (modexpInvFrame x).data.toList =
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE 32 32).data.toList ++
      (bytesNatBE 32 32).data.toList ++ (bytesNatBE x 32).data.toList ++
      (bytesNatBE (Midfall.Yul.blsR - 2) 32).data.toList ++
      (bytesNatBE Midfall.Yul.blsR 32).data.toList := by
  unfold modexpInvFrame modexpFrame
  simp [bytesOfWords, bytesAppend, Midfall.Yul.wordBytes, Bytes.empty, List.append_assoc]

/-- **THE SIX-STORE FRAME EQUALITY**: `scalar_inv`'s six stores read back as exactly the
    frame `modexpInv_correct` parses. -/
theorem mxMem_frame (mem : Nat → UInt8) (p : Nat) (x : U256) :
    readBytes (mxMem mem p x) p 192 = (modexpInvFrame x.toNat).data.toList := by
  rw [mxMem_read192, ← modexpInvFrame_data]

/-! ## 3. The `fail` call (the two guard arms and the staticcall guards) -/

/-- **THE `fail` CALL AT AN ARBITRARY VARIABLE SELECTOR.** A run of `fail(sel)` in any scope stack
    that resolves `fail` to the helper halts with a revert record. This is
    `TraceReturn.tr_fail_reverts` with `Expr.var "sel"` in place of `trErrExpr R.consts`; only the
    selector's non-halting is used, never its value. -/
theorem fail_expr_var {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st : EvmState} {r : EResult (Bridge.Dialect c g)}
    {sel : String} (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : Step (Bridge.Dialect c g) funs V st
        (Code.expr (Expr.call "fail" [Expr.var sel])) (Res.eres r)) :
    ∃ st₂, r = .halt st₂ ∧ Reverted st₂ := by
  cases h with
  | callOk hargs hlookup' hlen hbody ho =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          obtain ⟨ho', hrev⟩ := Blocks.TraceReturn.tr_fail_body hstmts
          cases ho with
          | inl hn =>
              exact absurd (hn.symm.trans ho')
                (by decide : (Outcome.normal : Outcome) ≠ Outcome.halt)
          | inr hl =>
              exact absurd (hl.symm.trans ho')
                (by decide : (Outcome.leave : Outcome) ≠ Outcome.halt)
  | callHalt hargs hlookup' hlen hbody =>
      rw [hlookup] at hlookup'
      cases hlookup'
      cases hbody with
      | block hstmts =>
          exact ⟨_, rfl, (Blocks.TraceReturn.tr_fail_body hstmts).2⟩
  | callArgsHalt hargs =>
      exact (Blocks.TraceReturn.trArgs1_halt_inv hargs
        (fun _ hh => Blocks.TraceReturn.trExprVar_ne_halts hh)).elim

/-- **THE FAIL EFFECT**: every run of the `fail(sel)` statement halts reverted. -/
theorem fail_call_reverts {funs funs' : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome} {sel : String}
    (hlookup : lookupFun funs "fail" = some (failFDecl, funs'))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.call "fail" [Expr.var sel])) V' st' o) :
    o = .halt ∧ Reverted st' := by
  cases h with
  | exprStmt hex =>
      obtain ⟨st₂, hr, hrev⟩ := fail_expr_var hlookup hex
      exact absurd hr (by simp)
  | exprStmtHalt hex =>
      obtain ⟨st₂, hr, hrev⟩ := fail_expr_var hlookup hex
      cases hr
      exact ⟨rfl, hrev⟩

/-! ## 4. The six-store contract: mstore plumbing -/

/-- The `scalar_inv` frame with the exponent word kept symbolic (`fv - 2`). -/
def mxMemFr (mem : Nat → UInt8) (p : Nat) (x fv : U256) : Nat → UInt8 :=
  storeWord (storeWord (storeWord (storeWord (storeWord (storeWord mem p 32)
    (p + 32) 32) (p + 64) 32) (p + 96) x) (p + 128) (fv - 2)) (p + 160) fv

/-- Evaluating `add(var x, lit n)` gives `pv + ofNat n` and leaves the state unchanged. -/
theorem eval_add_var_lit {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (n : Nat) (pv : U256) (hp : VEnv.get V x = some pv)
    {a : U256} (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.add [Expr.var x, Expr.lit (Literal.number n)]) (.vals [a] st')) :
    a = pv + BitVec.ofNat 256 n ∧ st' = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hhead =>
          cases hnil with
          | argsCons hnil2 htail =>
              cases hnil2 with
              | argsNil =>
                  cases htail with
                  | lit =>
                      cases hhead with
                      | var hget =>
                          rename_i v
                          have hv : v = pv := Option.some.inj (hget.symm.trans hp)
                          subst hv
                          simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
                          exact ⟨hbi.1.symm, hbi.2.symm⟩

/-- The address of an `add(var p, lit n)` after evaluation. -/
theorem toNat_add_ofNat (a : U256) (n : Nat) (h : a.toNat + n < 2 ^ 256) :
    (a + BitVec.ofNat 256 n).toNat = a.toNat + n := by
  have hn : n < 2 ^ 256 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt]
  omega

/-- `add(var, lit)` never halts. -/
theorem expr_add_var_lit_ne_halts {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.add [Expr.var x, Expr.lit (Literal.number n)]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hhead =>
          cases hnil with
          | argsCons hnil2 htail =>
              cases hnil2 with
              | argsNil =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => exact (trArgs1_halt_inv h (fun _ hh => trExprLit_ne_halts hh)).elim
      | argsHeadHalt _ h => exact trExprVar_ne_halts h

/-- `sub(var, lit)` never halts. -/
theorem expr_sub_var_lit_ne_halts {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (n : Nat) :
    ¬ EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.var x, Expr.lit (Literal.number n)]) (.halt st') := by
  intro h
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hhead =>
          cases hnil with
          | argsCons hnil2 htail =>
              cases hnil2 with
              | argsNil =>
                  simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => exact (trArgs1_halt_inv h (fun _ hh => trExprLit_ne_halts hh)).elim
      | argsHeadHalt _ h => exact trExprVar_ne_halts h

/-- A word store never halts, for any address/value expressions that themselves never halt. -/
theorem exec_mstore_normal {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) {V V' : VEnv (Bridge.Dialect c g)}
    {st st' : EvmState} {o : Outcome} {addr val : Expr EVM.Op}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore [addr, val])) V' st' o)
    (haddr : ∀ (st₁ st₂ : EvmState), EvalExpr (Bridge.Dialect c g) funs V st₁ addr (.halt st₂) → False)
    (hval : ∀ (st₁ st₂ : EvmState), EvalExpr (Bridge.Dialect c g) funs V st₁ val (.halt st₂) → False) :
    o = .normal := by
  cases h with
  | exprStmt _ => rfl
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hnil hhead =>
              cases hnil with
              | argsCons hnil2 htail =>
                  cases hnil2 with
                  | argsNil =>
                      simp [Bridge.Dialect, builtinWithExternal, stepOp] at hbi
      | builtinArgsHalt hargs =>
          cases hargs with
          | argsRestHalt h => exact (trArgs1_halt_inv h (fun _ hh => hval _ _ hh)).elim
          | argsHeadHalt _ h' => exact (haddr _ _ h').elim

/-- **ONE `mstore` STEP, WITH ITS EXPECTED ADDRESS AND VALUE.** A normal run updates only the
    memory to `storeWord st.memory aExp.toNat vExp`; the address and value expressions evaluate to
    the expected words and leave the state alone. -/
theorem exec_mstore_state {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) {V V1 : VEnv (Bridge.Dialect c g)}
    {st st1 : EvmState} {addr val : Expr EVM.Op} {aExp vExp : U256}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.exprStmt (Expr.builtin EVM.Op.mstore [addr, val])) V1 st1 .normal)
    (hval_st : ∀ (stV : EvmState) (v : U256),
      EvalExpr (Bridge.Dialect c g) funs V st val (.vals [v] stV) → stV = st)
    (haddr_st : ∀ (st0 stA : EvmState) (a : U256),
      EvalExpr (Bridge.Dialect c g) funs V st0 addr (.vals [a] stA) → stA = st0)
    (haddr_eq : ∀ (stA : EvmState) (a : U256),
      EvalExpr (Bridge.Dialect c g) funs V st addr (.vals [a] stA) → a = aExp)
    (hval_eq : ∀ (stV : EvmState) (v : U256),
      EvalExpr (Bridge.Dialect c g) funs V st val (.vals [v] stV) → v = vExp) :
    V1 = V ∧ st1.memory = storeWord st.memory aExp.toNat vExp ∧
      st1.env = st.env ∧ st1.halted = st.halted := by
  cases h with
  | exprStmt he =>
      cases he with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hargsVal hargsAddr =>
              cases hargsVal with
              | argsCons hnil hval =>
                  cases hnil with
                  | argsNil =>
                      have hvst := hval_st _ _ hval
                      rw [hvst] at hargsAddr
                      have ha := haddr_eq _ _ hargsAddr
                      have hv := hval_eq _ _ hval
                      subst ha
                      subst hv
                      have hast := haddr_st _ _ _ hargsAddr
                      rw [hast] at hbi
                      simp [Bridge.Dialect, builtinWithExternal, stepOp] at hbi
                      subst st1
                      exact ⟨rfl, rfl, rfl, rfl⟩

theorem eval_lit_eq (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (n : Nat) {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (Literal.number n)) (.vals [a] st')) :
    a = BitVec.ofNat 256 n ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

theorem eval_var_eq (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (xv : U256) (hx : VEnv.get V x = some xv) {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var x) (.vals [a] st')) :
    a = xv ∧ st' = st := by
  cases h with
  | var hget =>
      have ha : a = xv := Option.some.inj (hget.symm.trans hx)
      exact ⟨ha, rfl⟩

theorem eval_sub_var_lit (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    {st st' : EvmState} (x : String) (n : Nat) (pv : U256) (hp : VEnv.get V x = some pv)
    {a : U256} (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin EVM.Op.sub [Expr.var x, Expr.lit (Literal.number n)]) (.vals [a] st')) :
    a = pv - BitVec.ofNat 256 n ∧ st' = st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hhead =>
          cases hnil with
          | argsCons hnil2 htail =>
              cases hnil2 with
              | argsNil =>
                  cases htail with
                  | lit =>
                      cases hhead with
                      | var hget =>
                          rename_i v
                          have hv : v = pv := Option.some.inj (hget.symm.trans hp)
                          subst hv
                          simp [Bridge.Dialect, builtinWithExternal, stepOp, bin] at hbi
                          exact ⟨hbi.1.symm, hbi.2.symm⟩

/-- **THE SIX FRAME STORES.** Each of the six `mstore`s writes one word of
    `modexpInvFrame x`; the block leaves the environment and the halted flag alone and ends
    normally, with memory `mxMemFr st.memory p.toNat x fv`. -/
theorem modexpFrameStores_contract (funs : FunEnv (Bridge.Dialect c g)) (pv xv fv : U256)
    (hbound : pv.toNat + 192 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (GenAst.modexpFrameStores "p" (Expr.var "x") (Expr.var "FR_MODULUS")
        Midfall.Generator.templateConstantsDefault)
      (fun V st => VEnv.get V "p" = some pv ∧ VEnv.get V "x" = some xv ∧
        VEnv.get V "FR_MODULUS" = some fv)
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
                (fun stV v hv => (eval_sub_var_lit funs V (st := st4) "FR_MODULUS" 2 fv hfr hv).2)
                (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 128 pv hp ha).2)
                (fun stA a ha => (eval_add_var_lit funs V (st := st4) "p" 128 pv hp ha).1)
                (fun stV v hv => (eval_sub_var_lit funs V (st := st4) "FR_MODULUS" 2 fv hfr hv).1)
            subst V5
            rw [toNat_add_ofNat pv 128 (by omega)] at hmem5
            rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest5 with
                ⟨V6, st6, h6, hrest6⟩ | ⟨h6, hne6⟩
            · obtain ⟨hV6, hmem6, henv6, hhalt6⟩ :=
                exec_mstore_state (c := c) (g := g) funs h6
                  (fun stV v hv => (eval_var_eq funs V (st := st5) "FR_MODULUS" fv hfr hv).2)
                  (fun st0 stA a ha => (eval_add_var_lit funs V (st := st0) "p" 160 pv hp ha).2)
                  (fun stA a ha => (eval_add_var_lit funs V (st := st5) "p" 160 pv hp ha).1)
                  (fun stV v hv => (eval_var_eq funs V (st := st5) "FR_MODULUS" fv hfr hv).1)
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
                (fun s₁ s₂ hh => trExprVar_ne_halts hh)) hne6
          · exact absurd (exec_mstore_normal funs h5
              (fun s₁ s₂ hh => expr_add_var_lit_ne_halts funs V (st := s₁) (x := "p") (n := 128) hh)
              (fun s₁ s₂ hh => expr_sub_var_lit_ne_halts funs V (st := s₁) (x := "FR_MODULUS") (n := 2) hh)) hne5
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

#assert_axioms Midfall.LoweringV3.ScalarInv.mxMem_frame
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInv.fail_call_reverts
  [propext, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.ScalarInv.modexpFrameStores_contract
  [propext, Quot.sound] native []

end Midfall.LoweringV3.ScalarInv

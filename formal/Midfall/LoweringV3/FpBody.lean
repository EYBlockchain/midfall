import Midfall.LoweringV2.Blocks.EcPairing
set_option autoImplicit false

namespace Midfall.LoweringV2.Blocks.EcPairing

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV2.Blocks.TraceReturn
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.VKP

variable {c : ExternalCalls} {g : ExternalGas}

/-- The helper's entry environment, as the call rule builds it. -/
abbrev fpEntry (lhsW rhsW : U256) : VEnv (Bridge.Dialect c g) :=
  ["success", "lhs_mptr", "rhs_mptr"].zip [(1 : U256), lhsW, rhsW] ++
    bindZeros (Bridge.Dialect c g) ["ret"]

/-- **PHASE 1 OF THE `ec_pairing` BODY RUN - THE ENCODING PREFIX.** The first seven statements
    (`ret := success`; the `leave` guard skipping at 1; `let scratch`; the four `mcopy`s) run from
    the helper's entry environment to a state whose memory is the four copies and whose VEnv still
    binds the three parameters, `ret = 1` and `scratch = ofNat scratch`. -/
theorem ecPairing_prefix_run (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState)
    (lhsW rhsW : U256) (scratch g2 neg _gas : Nat) :
    ∃ (V3 : VEnv (Bridge.Dialect c g)) (st3 : EvmState),
      ExecStmts (Bridge.Dialect c g) funs (fpEntry (c := c) (g := g) lhsW rhsW) st
        [Stmt.assign ["ret"] (Expr.var "success"),
         Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) [Stmt.leave],
         Stmt.letDecl ["scratch"] (some (Expr.lit (.number scratch))),
         Stmt.exprStmt (Expr.builtin Op.mcopy
           [Expr.var "scratch", Expr.var "lhs_mptr", Expr.lit (.number 0x80)]),
         Stmt.exprStmt (Expr.builtin Op.mcopy
           [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x80)],
            Expr.lit (.number g2), Expr.lit (.number 0x100)]),
         Stmt.exprStmt (Expr.builtin Op.mcopy
           [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x180)],
            Expr.var "rhs_mptr", Expr.lit (.number 0x80)]),
         Stmt.exprStmt (Expr.builtin Op.mcopy
           [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x200)],
            Expr.lit (.number neg), Expr.lit (.number 0x100)])]
        V3 st3 .normal ∧
      st3.env = st.env ∧ st3.halted = st.halted ∧
      VEnv.get V3 "ret" = some (1 : U256) ∧
      VEnv.get V3 "scratch" = some (BitVec.ofNat 256 scratch) ∧
      VEnv.get V3 "lhs_mptr" = some lhsW ∧ VEnv.get V3 "rhs_mptr" = some rhsW := by
  -- V1: ret := success
  let V1 : VEnv (Bridge.Dialect c g) := VEnv.setMany (fpEntry (c := c) (g := g) lhsW rhsW) ["ret"] [1]
  have h1 : ExecStmt (Bridge.Dialect c g) funs (fpEntry (c := c) (g := g) lhsW rhsW) st
      (Stmt.assign ["ret"] (Expr.var "success")) V1 st .normal := by
    refine Step.assignVal ?_ rfl
    show EvalExpr (Bridge.Dialect c g) funs (fpEntry (c := c) (g := g) lhsW rhsW) st
      (Expr.var "success") (.vals [1] st)
    exact Step.var rfl
  -- V2: the leave guard skips at ret = 1
  have hz : EvalExpr (Bridge.Dialect c g) funs V1 st
      (Expr.builtin Op.iszero [Expr.var "ret"]) (.vals [0] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [Expr.var "ret"])
      (argvals := [(1 : U256)]) (rets := [0]) (st1 := st) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
        (Step.var (D := Bridge.Dialect c g) (v := (1 : U256)) rfl)) ?_
    simp only [builtinWithExternal, stepOp, un, b2w]
    rfl
  have h2 : ExecStmt (Bridge.Dialect c g) funs V1 st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) [Stmt.leave]) V1 st .normal :=
    Step.ifFalse hz rfl
  -- V2: let scratch
  let V2 : VEnv (Bridge.Dialect c g) := ["scratch"].zip [BitVec.ofNat 256 scratch] ++ V1
  have h3 : ExecStmt (Bridge.Dialect c g) funs V1 st
      (Stmt.letDecl ["scratch"] (some (Expr.lit (.number scratch)))) V2 st .normal := by
    refine Step.letVal (D := Bridge.Dialect c g) (vars := ["scratch"])
      (e := Expr.lit (.number scratch))
      (Step.lit (D := Bridge.Dialect c g) (l := Literal.number scratch)) rfl
  -- the four mcopy states
  let sc : U256 := BitVec.ofNat 256 scratch
  let st1 : EvmState := { touchMemory2 st (sc.toNat) ((0x80 : U256).toNat) lhsW.toNat
      ((0x80 : U256).toNat) with memory := copyWithin st.memory sc.toNat lhsW.toNat 0x80 }
  let st2 : EvmState := { touchMemory2 st1 ((sc + (0x80 : U256)).toNat) ((0x100 : U256).toNat)
      ((BitVec.ofNat 256 g2).toNat) ((0x100 : U256).toNat) with
    memory := copyWithin st1.memory (sc + (0x80 : U256)).toNat (BitVec.ofNat 256 g2).toNat 0x100 }
  let st3 : EvmState := { touchMemory2 st2 ((sc + (0x180 : U256)).toNat) ((0x80 : U256).toNat)
      rhsW.toNat ((0x80 : U256).toNat) with
    memory := copyWithin st2.memory (sc + (0x180 : U256)).toNat rhsW.toNat 0x80 }
  let st4 : EvmState := { touchMemory2 st3 ((sc + (0x200 : U256)).toNat) ((0x100 : U256).toNat)
      ((BitVec.ofNat 256 neg).toNat) ((0x100 : U256).toNat) with
    memory := copyWithin st3.memory (sc + (0x200 : U256)).toNat (BitVec.ofNat 256 neg).toNat 0x100 }
  have hmc1 : ExecStmt (Bridge.Dialect c g) funs V2 st
      (Stmt.exprStmt (Expr.builtin Op.mcopy
        [Expr.var "scratch", Expr.var "lhs_mptr", Expr.lit (.number 0x80)])) V2 st1 .normal := by
    refine Step.exprStmt (D := Bridge.Dialect c g) ?_
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (args := [Expr.var "scratch", Expr.var "lhs_mptr", Expr.lit (.number 0x80)])
      (argvals := [sc, lhsW, (0x80 : U256)]) (rets := []) (st1 := st) (st2 := st1)
      (Step.argsCons (D := Bridge.Dialect c g)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x80)))
          (Step.var (D := Bridge.Dialect c g) (v := lhsW) rfl))
        (Step.var (D := Bridge.Dialect c g) (v := sc) rfl)) ?_
    simp only [builtinWithExternal, stepOp]
    rfl
  have hmc2 : ExecStmt (Bridge.Dialect c g) funs V2 st1
      (Stmt.exprStmt (Expr.builtin Op.mcopy
        [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x80)],
         Expr.lit (.number g2), Expr.lit (.number 0x100)])) V2 st2 .normal := by
    refine Step.exprStmt (D := Bridge.Dialect c g) ?_
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (args := [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x80)],
        Expr.lit (.number g2), Expr.lit (.number 0x100)])
      (argvals := [sc + (0x80 : U256), BitVec.ofNat 256 g2, (0x100 : U256)])
      (rets := []) (st1 := st1) (st2 := st2)
      (Step.argsCons (D := Bridge.Dialect c g)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x100)))
          (Step.lit (D := Bridge.Dialect c g) (l := Literal.number g2)))
        ?_) ?_
    · refine Step.builtinOk (D := Bridge.Dialect c g)
        (args := [Expr.var "scratch", Expr.lit (.number 0x80)])
        (argvals := [sc, (0x80 : U256)]) (rets := [sc + (0x80 : U256)])
        (st1 := st1) (st2 := st1)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x80)))
          (Step.var (D := Bridge.Dialect c g) (v := sc) rfl)) ?_
      rfl
    · simp only [builtinWithExternal, stepOp]
      rfl
  have hmc3 : ExecStmt (Bridge.Dialect c g) funs V2 st2
      (Stmt.exprStmt (Expr.builtin Op.mcopy
        [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x180)],
         Expr.var "rhs_mptr", Expr.lit (.number 0x80)])) V2 st3 .normal := by
    refine Step.exprStmt (D := Bridge.Dialect c g) ?_
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (args := [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x180)],
        Expr.var "rhs_mptr", Expr.lit (.number 0x80)])
      (argvals := [sc + (0x180 : U256), rhsW, (0x80 : U256)])
      (rets := []) (st1 := st2) (st2 := st3)
      (Step.argsCons (D := Bridge.Dialect c g)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x80)))
          (Step.var (D := Bridge.Dialect c g) (v := rhsW) rfl))
        ?_) ?_
    · refine Step.builtinOk (D := Bridge.Dialect c g)
        (args := [Expr.var "scratch", Expr.lit (.number 0x180)])
        (argvals := [sc, (0x180 : U256)]) (rets := [sc + (0x180 : U256)])
        (st1 := st2) (st2 := st2)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x180)))
          (Step.var (D := Bridge.Dialect c g) (v := sc) rfl)) ?_
      rfl
    · simp only [builtinWithExternal, stepOp]
      rfl
  have hmc4 : ExecStmt (Bridge.Dialect c g) funs V2 st3
      (Stmt.exprStmt (Expr.builtin Op.mcopy
        [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x200)],
         Expr.lit (.number neg), Expr.lit (.number 0x100)])) V2 st4 .normal := by
    refine Step.exprStmt (D := Bridge.Dialect c g) ?_
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (args := [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x200)],
        Expr.lit (.number neg), Expr.lit (.number 0x100)])
      (argvals := [sc + (0x200 : U256), BitVec.ofNat 256 neg, (0x100 : U256)])
      (rets := []) (st1 := st3) (st2 := st4)
      (Step.argsCons (D := Bridge.Dialect c g)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x100)))
          (Step.lit (D := Bridge.Dialect c g) (l := Literal.number neg)))
        ?_) ?_
    · refine Step.builtinOk (D := Bridge.Dialect c g)
        (args := [Expr.var "scratch", Expr.lit (.number 0x200)])
        (argvals := [sc, (0x200 : U256)]) (rets := [sc + (0x200 : U256)])
        (st1 := st3) (st2 := st3)
        (Step.argsCons (D := Bridge.Dialect c g)
          (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
            (Step.lit (D := Bridge.Dialect c g) (l := Literal.number 0x200)))
          (Step.var (D := Bridge.Dialect c g) (v := sc) rfl)) ?_
      rfl
    · simp only [builtinWithExternal, stepOp]
      rfl
  refine ⟨V2, st4, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact Step.seqCons h1 (Step.seqCons h2 (Step.seqCons h3 (Step.seqCons hmc1
      (Step.seqCons hmc2 (Step.seqCons hmc3 (Step.seqCons hmc4 Step.seqNil))))))
  · rfl
  · rfl
  · rfl
  · rfl


end Midfall.LoweringV2.Blocks.EcPairing

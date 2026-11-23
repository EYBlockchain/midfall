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



/-- **PHASE 2 OF THE `ec_pairing` BODY RUN - THE STATICCALL STEP.** Given the honest response at the
    request the six arguments form (the input is the 768-byte scratch read), the helper's
    `ret := staticcall(PAIRING_GAS_2PAIR, 0x0f, scratch, 768, scratch, 32)` statement has a normal
    run that writes `resp.flag` to `ret` and leaves `finishCall`'s memory. The response itself is the
    caller's obligation (`honestOf` answers at 0x0f; the product/validity facts are its
    preconditions). -/
theorem ecPairing_staticcall_step (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (scratch gas addr frameBytes outBytes : Nat)
    (resp : EVM.CallResponse)
    (hscratch : VEnv.get V "scratch" = some (BitVec.ofNat 256 scratch))
    (hcall : c.Call (show YulSemantics.EVM.CallRequest from
        { kind := YulSemantics.EVM.CallKind.staticcall, gas := BitVec.ofNat 256 gas,
          target := BitVec.ofNat 256 addr, value := 0,
          input := readBytes st.memory (BitVec.ofNat 256 scratch).toNat (BitVec.ofNat 256 frameBytes).toNat }) st resp) :
    ∃ st' : EvmState,
      ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.assign ["ret"] (Expr.builtin Op.staticcall
          [Expr.lit (.number gas), Expr.lit (.number addr), Expr.var "scratch",
           Expr.lit (.number frameBytes), Expr.var "scratch", Expr.lit (.number outBytes)]))
        (VEnv.setMany V ["ret"] [resp.flag]) st' .normal ∧
      st' = finishCall .staticcall st resp (BitVec.ofNat 256 scratch).toNat
        (BitVec.ofNat 256 frameBytes).toNat (BitVec.ofNat 256 scratch).toNat
        (BitVec.ofNat 256 outBytes).toNat := by
  let sc : U256 := BitVec.ofNat 256 scratch
  let gv : U256 := BitVec.ofNat 256 gas
  let av : U256 := BitVec.ofNat 256 addr
  let fv : U256 := BitVec.ofNat 256 frameBytes
  let ov : U256 := BitVec.ofNat 256 outBytes
  let st' : EvmState := finishCall .staticcall st resp sc.toNat fv.toNat sc.toNat ov.toNat
  have hOut : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number outBytes))
      (.vals [ov] st) := Step.lit
  have hScratch2 : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var "scratch")
      (.vals [sc] st) := Step.var hscratch
  have hFrame : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number frameBytes))
      (.vals [fv] st) := Step.lit
  have hScratch1 : EvalExpr (Bridge.Dialect c g) funs V st (Expr.var "scratch")
      (.vals [sc] st) := Step.var hscratch
  have hAddr : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number addr))
      (.vals [av] st) := Step.lit
  have hGas : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number gas))
      (.vals [gv] st) := Step.lit
  have hargs : Step (Bridge.Dialect c g) funs V st
      (.args [Expr.lit (.number gas), Expr.lit (.number addr), Expr.var "scratch",
        Expr.lit (.number frameBytes), Expr.var "scratch", Expr.lit (.number outBytes)])
      (.eres (.vals [gv, av, sc, fv, sc, ov] st)) :=
    Step.argsCons
      (Step.argsCons
        (Step.argsCons
          (Step.argsCons
            (Step.argsCons
              (Step.argsCons Step.argsNil hOut) hScratch2) hFrame) hScratch1) hAddr) hGas
  refine ⟨st', ?_, rfl⟩
  refine Step.assignVal (D := Bridge.Dialect c g) (vars := ["ret"])
    (e := Expr.builtin Op.staticcall
      [Expr.lit (.number gas), Expr.lit (.number addr), Expr.var "scratch",
       Expr.lit (.number frameBytes), Expr.var "scratch", Expr.lit (.number outBytes)])
    (vals := [resp.flag]) ?_ rfl
  refine Step.builtinOk (D := Bridge.Dialect c g) (op := Op.staticcall)
    (args := [Expr.lit (.number gas), Expr.lit (.number addr), Expr.var "scratch",
      Expr.lit (.number frameBytes), Expr.var "scratch", Expr.lit (.number outBytes)])
    (argvals := [gv, av, sc, fv, sc, ov]) (rets := [resp.flag]) (st1 := st) (st2 := st')
    hargs ?_
  show (Bridge.Dialect c g).Builtin Op.staticcall [gv, av, sc, fv, sc, ov] st
    (.ok [resp.flag] st')
  refine ⟨resp, ?_, rfl⟩
  change c.Call (show YulSemantics.EVM.CallRequest from
    { kind := YulSemantics.EVM.CallKind.staticcall, gas := gv, target := av, value := 0,
      input := readBytes st.memory sc.toNat fv.toNat }) st resp
  exact hcall



/-- `VEnv.set` at a different name leaves a lookup untouched. -/
theorem fp_venv_get_set_ne {D : YulSemantics.Dialect} [DecidableEq D.Value] {V : VEnv D}
    {x y : Ident} {v : D.Value} (h : y ≠ x) :
    VEnv.get (VEnv.set V x v) y = VEnv.get V y := by
  induction V with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨x', v'⟩ := p
      by_cases hx : x' = x
      · subst hx
        have hxy : decide (x' = y) = false := by
          rw [decide_eq_false]; exact fun hh => h hh.symm
        simp only [VEnv.set, ite_true, VEnv.get, List.find?, hxy]
      · rw [VEnv.set, ite_eq_right hx]
        by_cases hy : x' = y
        · subst hy
          simp only [VEnv.get, List.find?]
          rfl
        · have hxy : decide (x' = y) = false := by
            rw [decide_eq_false]; exact hy
          simp only [VEnv.get, List.find?, hxy]
          exact ih

/-- **PHASE 3 OF THE `ec_pairing` BODY RUN - THE POST-STATICCALL FRAME.** When the answer word is
    1 (the honest response on a valid frame with a true product), the five statements after the
    staticcall run normally with `ret = 1`; the two `fail` arms are not taken. -/
theorem ecPairing_tail_normal (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState)
    (V : VEnv (Bridge.Dialect c g)) (scratch errProof : Nat)
    (hret : VEnv.get V "ret" = some (1 : U256))
    (hscratch : VEnv.get V "scratch" = some (BitVec.ofNat 256 scratch))
    (hlen : st.returndata.length = 32)
    (hload : loadWord st.memory scratch = 1)
    (hscratchWin : scratch < 2 ^ 256) :
    ∃ (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState),
      ExecStmts (Bridge.Dialect c g) funs V st
        [Stmt.assign ["ret"] (Expr.builtin Op.and
           [Expr.var "ret", Expr.builtin Op.eq
             [Expr.builtin Op.returndatasize [], Expr.lit (.number 32)]]),
         Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
           [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errProof)])],
         Stmt.assign ["ret"] (Expr.builtin Op.and
           [Expr.var "ret", Expr.builtin Op.eq
             [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)]]),
         Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
           [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errProof)])],
         Stmt.assign ["ret"] (Expr.lit (.number 1))] V' st' .normal ∧
      st' = touchMemory st scratch 32 ∧ VEnv.get V' "ret" = some (1 : U256) := by
  let V1 : VEnv (Bridge.Dialect c g) := VEnv.setMany V ["ret"] [1]
  have hrd : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.returndatasize []) (.vals [(BitVec.ofNat 256 st.returndata.length : U256)] st) :=
    Step.builtinOk (D := Bridge.Dialect c g) Step.argsNil
      (by simp only [builtinWithExternal, stepOp, rd0])
  have hlit32 : EvalExpr (Bridge.Dialect c g) funs V st (Expr.lit (.number 32))
      (.vals [(32 : U256)] st) := Step.lit
  have h1 : b2w (BitVec.ofNat 256 st.returndata.length = (32 : U256)) = 1 := by
    rw [hlen]; decide
  have heq1 : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.eq [Expr.builtin Op.returndatasize [], Expr.lit (.number 32)])
      (.vals [1] st) := by
    have h := Step.builtinOk (D := Bridge.Dialect c g) (op := Op.eq)
      (args := [Expr.builtin Op.returndatasize [], Expr.lit (.number 32)])
      (argvals := [BitVec.ofNat 256 st.returndata.length, (32 : U256)]) (rets := [1])
      (st1 := st) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g)
        Step.argsNil hlit32) hrd)
      (by simp only [builtinWithExternal, stepOp, bin]; rw [h1])
    simpa only [h1] using h
  have hand1 : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.and [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.returndatasize [], Expr.lit (.number 32)]]) (.vals [1] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g)
        Step.argsNil heq1) (Step.var hret)) ?_
    simp only [builtinWithExternal, stepOp, bin]; simp [b2w]
  have hs1 : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["ret"] (Expr.builtin Op.and
        [Expr.var "ret", Expr.builtin Op.eq
          [Expr.builtin Op.returndatasize [], Expr.lit (.number 32)]])) V1 st .normal :=
    Step.assignVal hand1 rfl
  have hret1 : VEnv.get V1 "ret" = some (1 : U256) := by
    rw [show V1 = VEnv.set V "ret" (1 : U256) by dsimp only [V1]; rfl]
    exact EcPairing.venv_get_set_same hret
  have hz1 : EvalExpr (Bridge.Dialect c g) funs V1 st
      (Expr.builtin Op.iszero [Expr.var "ret"]) (.vals [0] st) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [Expr.var "ret"])
      (argvals := [(1 : U256)]) (rets := [0]) (st1 := st) (st2 := st)
      (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
        (Step.var (D := Bridge.Dialect c g) (v := (1 : U256)) hret1)) ?_
    simp only [builtinWithExternal, stepOp, un, b2w]; rfl
  have hg1 : ExecStmt (Bridge.Dialect c g) funs V1 st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errProof)])]) V1 st .normal :=
    Step.ifFalse hz1 rfl
  let V2 : VEnv (Bridge.Dialect c g) := VEnv.setMany V1 ["ret"] [1]
  have hml : EvalExpr (Bridge.Dialect c g) funs V1 st
      (Expr.builtin Op.mload [Expr.var "scratch"])
      (.vals [1] (touchMemory st scratch 32)) := by
    have hsv : VEnv.get V1 "scratch" = some (BitVec.ofNat 256 scratch) := by
      rw [show V1 = VEnv.set V "ret" (1 : U256) by dsimp only [V1]; rfl,
        fp_venv_get_set_ne (D := Bridge.Dialect c g)
          (x := "ret") (y := "scratch") (v := (1 : U256)) (by decide)]
      exact hscratch
    have hv : EvalExpr (Bridge.Dialect c g) funs V1 st (Expr.var "scratch")
        (.vals [BitVec.ofNat 256 scratch] st) := Step.var hsv
    have hto : (BitVec.ofNat 256 scratch).toNat = scratch := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hscratchWin]
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (args := [Expr.var "scratch"]) (argvals := [BitVec.ofNat 256 scratch])
      (rets := [1]) (st1 := st) (st2 := touchMemory st scratch 32)
      (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil hv) ?_
    simp only [builtinWithExternal, stepOp]
    rw [hto, hload]
  have hlit1 : EvalExpr (Bridge.Dialect c g) funs V1 st (Expr.lit (.number 1))
      (.vals [(1 : U256)] st) :=
    Step.lit (D := Bridge.Dialect c g) (funs := funs) (V := V1) (st := st)
      (l := Literal.number 1)
  have heq2 : EvalExpr (Bridge.Dialect c g) funs V1 st
      (Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)])
      (.vals [1] (touchMemory st scratch 32)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (op := Op.eq)
      (args := [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)])
      (argvals := [(1 : U256), (1 : U256)]) (rets := [(1 : U256)])
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g)
        Step.argsNil hlit1) hml) ?_
    simp only [builtinWithExternal, stepOp, bin]; simp [b2w]
  have hand2 : EvalExpr (Bridge.Dialect c g) funs V1 st
      (Expr.builtin Op.and [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)]])
      (.vals [1] (touchMemory st scratch 32)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g)
      (Step.argsCons (D := Bridge.Dialect c g) (Step.argsCons (D := Bridge.Dialect c g)
        Step.argsNil heq2) (Step.var hret1)) ?_
    simp only [builtinWithExternal, stepOp, bin]; simp [b2w]
  have hs2 : ExecStmt (Bridge.Dialect c g) funs V1 st
      (Stmt.assign ["ret"] (Expr.builtin Op.and
        [Expr.var "ret", Expr.builtin Op.eq
          [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)]])) V2
      (touchMemory st scratch 32) .normal :=
    Step.assignVal hand2 rfl
  have hret2 : VEnv.get V2 "ret" = some (1 : U256) := by
    rw [show V2 = VEnv.set V1 "ret" (1 : U256) by dsimp only [V2]; rfl]
    exact EcPairing.venv_get_set_same hret1
  have hz2 : EvalExpr (Bridge.Dialect c g) funs V2 (touchMemory st scratch 32)
      (Expr.builtin Op.iszero [Expr.var "ret"]) (.vals [0] (touchMemory st scratch 32)) := by
    refine Step.builtinOk (D := Bridge.Dialect c g) (args := [Expr.var "ret"])
      (argvals := [(1 : U256)]) (rets := [0]) (st1 := touchMemory st scratch 32)
      (st2 := touchMemory st scratch 32)
      (Step.argsCons (D := Bridge.Dialect c g) Step.argsNil
        (Step.var (D := Bridge.Dialect c g) (v := (1 : U256)) hret2)) ?_
    simp only [builtinWithExternal, stepOp, un, b2w]; rfl
  have hg2 : ExecStmt (Bridge.Dialect c g) funs V2 (touchMemory st scratch 32)
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
        [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errProof)])]) V2
      (touchMemory st scratch 32) .normal :=
    Step.ifFalse hz2 rfl
  let V3 : VEnv (Bridge.Dialect c g) := VEnv.setMany V2 ["ret"] [1]
  have hs3 : ExecStmt (Bridge.Dialect c g) funs V2 (touchMemory st scratch 32)
      (Stmt.assign ["ret"] (Expr.lit (.number 1))) V3 (touchMemory st scratch 32) .normal := by
    refine Step.assignVal (D := Bridge.Dialect c g) (vars := ["ret"])
      (e := Expr.lit (.number 1)) (vals := [(1 : U256)]) ?_ rfl
    exact Step.lit (D := Bridge.Dialect c g) (funs := funs) (V := V2)
      (st := touchMemory st scratch 32) (l := Literal.number 1)
  have hret3 : VEnv.get V3 "ret" = some (1 : U256) := by
    rw [show V3 = VEnv.set V2 "ret" (1 : U256) by dsimp only [V3]; rfl]
    exact EcPairing.venv_get_set_same hret2
  refine ⟨V3, touchMemory st scratch 32, ?_, rfl, hret3⟩
  exact Step.seqCons hs1 (Step.seqCons hg1 (Step.seqCons hs2 (Step.seqCons hg2
    (Step.seqCons hs3 Step.seqNil))))


end Midfall.LoweringV2.Blocks.EcPairing

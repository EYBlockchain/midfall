import Midfall.LoweringV3.EndToEndAlgebra
set_option autoImplicit false
set_option maxRecDepth 100000
open Midfall Midfall.Halo2 Midfall.Lowering Midfall.Lowering.GenAst YulSemantics YulSemantics.EVM
namespace Midfall.LoweringV3

def commonG1Inline (err hi lo : Nat) : Block EVM.Op :=
  [ ylet "x_hi_word" (yop EVM.Op.calldataload [yvar "cptr"])
  , ylet "x_lo" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x20]])
  , ylet "y_hi_word" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x40]])
  , ylet "y_lo" (yop EVM.Op.calldataload [yop EVM.Op.add [yvar "cptr", ylit 0x60]])
  , yif (yop EVM.Op.shr [ylit 128, yvar "x_hi_word"]) [yexpr (ycall "fail" [ylit err])]
  , yif (yop EVM.Op.shr [ylit 128, yvar "y_hi_word"]) [yexpr (ycall "fail" [ylit err])]
  , ylet "x_hi" (yop EVM.Op.and [yvar "x_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
  , ylet "y_hi" (yop EVM.Op.and [yvar "y_hi_word", ylit 0xffffffffffffffffffffffffffffffff])
  , yif (yop EVM.Op.iszero [yop EVM.Op.or
      [ yop EVM.Op.lt [yvar "x_hi", ylit hi]
      , yop EVM.Op.and [yop EVM.Op.eq [yvar "x_hi", ylit hi],
          yop EVM.Op.iszero [yop EVM.Op.gt [yvar "x_lo", ylit lo]]] ]])
      [yexpr (ycall "fail" [ylit err])]
  , yif (yop EVM.Op.iszero [yop EVM.Op.or
      [ yop EVM.Op.lt [yvar "y_hi", ylit hi]
      , yop EVM.Op.and [yop EVM.Op.eq [yvar "y_hi", ylit hi],
          yop EVM.Op.iszero [yop EVM.Op.gt [yvar "y_lo", ylit lo]]] ]])
      [yexpr (ycall "fail" [ylit err])]
  , yexpr (yop EVM.Op.calldatacopy [yvar "buf_len", yvar "cptr", ylit 0x80])
  , yset "ret" (yop EVM.Op.add [yvar "buf_len", ylit 0x80]) ]

theorem commonG1_inline (consts : Inline.Consts) (err hi lo : Nat)
    (he : consts.lookup "ERR_BAD_POINT_ENCODING" = some err)
    (hh : consts.lookup "BLS_P_HI" = some hi)
    (hl : consts.lookup "BLS_P_MINUS_ONE_LO" = some lo) :
    Inline.inlineContractConstants consts GenAst.emitCommonUncompressedG1 =
      [Stmt.funDef "common_uncompressed_g1" ["buf_len", "cptr"] ["ret"]
        (commonG1Inline err hi lo)] := by
  rw [show Inline.inlineContractConstants consts GenAst.emitCommonUncompressedG1 =
      (Inline.inlineStep (Inline.inlineScan 63 consts) consts []
        GenAst.emitCommonUncompressedG1).blks from rfl]
  simp only [GenAst.emitCommonUncompressedG1, commonG1Inline, GenAst.ylet, GenAst.ylit,
    GenAst.yexpr, GenAst.yop, GenAst.yvar, GenAst.yset, GenAst.yif, GenAst.yfun, GenAst.ycall,
    GenAst.g1CoordRangeCheck,
    Inline.inlineStep, Inline.exprFuel, Inline.shadowed, Inline.boundOf, List.foldl_cons, List.foldl_nil, List.append_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    Inline.inlineStmtStep.eq_2, Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_5,
    Inline.inlineStmtStep.eq_4, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5,
    he, hh, hl, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 63 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 62 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons, List.foldl_nil, List.append_nil,
    List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
    Inline.inlineStmtStep.eq_3, Inline.inlineStmtStep.eq_5, Inline.inlineStmtStep.eq_4,
    Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_5,
    he, hh, hl, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 62 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 61 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons,
    List.foldl_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.cons_append, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    he, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]
  rw [show ∀ (sh : List String) (b : List (Stmt EVM.Op)),
      (Inline.inlineScan 62 consts sh b).blks =
        (Inline.inlineStep (Inline.inlineScan 61 consts) consts sh b).blks
      from fun _ _ => rfl]
  simp only [Inline.inlineStep, Inline.exprFuel, Inline.boundOf, List.foldl_cons,
    List.foldl_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.cons_append, Inline.inlineStmtStep.eq_8, Inline.inlineStmtStep.eq_9,
    Inline.inExpr.eq_2, Inline.inExpr.eq_3, Inline.inExpr.eq_4,
    he, Option.map_some, Option.map_none, List.map_cons, List.map_nil]
  simp [Inline.shadowed]

end Midfall.LoweringV3

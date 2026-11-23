/-
  Midfall.LoweringV2.Blocks.EcPairing

  A11 STEP-1 FOUNDATION: THE `ec_pairing` HELPER BODY, AS THE SCOPE ACTUALLY RESOLVES IT.

  The FinalPairing row has to reason about the helper's THIRTEEN-statement body. The inliner
  traverses every helper body before `ec_pairing`, so the elaborator's `rfl`/`Meta.whnf` cannot
  reach the declaration (measured: deterministic-whnf timeout). `kernel_rfl` (the evidence's
  T3.9/LagrangeRows device) defers the definitional check to the KERNEL, which is lazy and does
  not time out. The three equations below are the result: the scope lookup, the explicit body,
  and the `copyWithin` window lemmas the frame walk needs.

  EMITTER TRUTH (checked against `GenAst.emitEcPairing` and the `ecPairing_snapshot` gate): the
  helper's last assignment is `ret := 1`, AFTER the `and(ret, eq(mload(scratch), 1))` guard. So
  on a normal return `ret` is 1, not `success &&& answer`; the `and` word only decides whether
  the helper REVERTS. The contract must use that fact, not the trace-render description.

  No frozen/vendor file is touched. No statement here adds a hypothesis to a row or ValidV3.
-/
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Blocks.VkLoading
import Midfall.Tools.Done
import Midfall.Yul.VKP

set_option autoImplicit false

namespace Midfall.LoweringV2.Blocks.EcPairing

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV2.Blocks.TraceReturn
open Midfall.Yul.Wp Midfall.Yul.WpBridge Midfall.Yul.WpTac Midfall.Yul.VKP

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
  {c : ExternalCalls} {g : ExternalGas}

open Lean Elab Tactic Meta in
/-- Close an equality by `Eq.refl`, leaving the definitional check to the KERNEL. The elaborator's
    `rfl` runs `Meta.whnf`, which times out on the inlined helper block; the kernel reducer does
    not. No axiom is added. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, _, rhs) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  goal.assign (← mkEqRefl rhs)

/-- The single function body an emitter prints, constants inlined (a helper's code). -/
def helperBody (consts : Inline.Consts) (emit : Block EVM.Op) : Block EVM.Op :=
  match Inline.inlineContractConstants consts emit with
  | [Stmt.funDef _ _ _ body] => body
  | _ => []

/-- The inlined constant site, in the two shapes the inliner can leave. -/
def ecVal (consts : Inline.Consts) (name : String) : Expr EVM.Op :=
  match consts.lookup name with
  | some v => Expr.lit (.number v)
  | none => Expr.var name

/-- The explicit `ec_pairing` body, at a symbolic constant table and the plan's scratch pointer.
    `success`, `lhs_mptr`, `rhs_mptr`, `ret` and `scratch` are the helper's own names and stay
    variables (the inliner shadows them); the five interpolated names are `ecVal` sites. -/
def ecPairingBody (consts : Inline.Consts) (scratch addr frameBytes outBytes : Nat) :
    Block EVM.Op :=
  [ Stmt.assign ["ret"] (Expr.var "success"),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) [Stmt.leave],
    Stmt.letDecl ["scratch"] (some (Expr.lit (.number scratch))),
    Stmt.exprStmt (Expr.builtin Op.mcopy
      [Expr.var "scratch", Expr.var "lhs_mptr", Expr.lit (.number 0x80)]),
    Stmt.exprStmt (Expr.builtin Op.mcopy
      [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x80)],
       ecVal consts "G2_BASE_MPTR", Expr.lit (.number 0x100)]),
    Stmt.exprStmt (Expr.builtin Op.mcopy
      [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x180)],
       Expr.var "rhs_mptr", Expr.lit (.number 0x80)]),
    Stmt.exprStmt (Expr.builtin Op.mcopy
      [Expr.builtin Op.add [Expr.var "scratch", Expr.lit (.number 0x200)],
       ecVal consts "NEG_S_G2_BASE_MPTR", Expr.lit (.number 0x100)]),
    Stmt.assign ["ret"] (Expr.builtin Op.staticcall
      [ecVal consts "PAIRING_GAS_2PAIR", Expr.lit (.number addr),
       Expr.var "scratch", Expr.lit (.number frameBytes),
       Expr.var "scratch", Expr.lit (.number outBytes)]),
    Stmt.assign ["ret"] (Expr.builtin Op.and
      [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.returndatasize [], Expr.lit (.number outBytes)]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
      [Stmt.exprStmt (Expr.call "fail" [ecVal consts "ERR_PRECOMPILE_FAILED"])],
    Stmt.assign ["ret"] (Expr.builtin Op.and
      [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
      [Stmt.exprStmt (Expr.call "fail" [ecVal consts "ERR_PROOF_REJECTED"])],
    Stmt.assign ["ret"] (Expr.lit (.number 1)) ]

/-- The declaration `R.scope` actually resolves for `ec_pairing`. -/
def ecPairingDecl (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) :
    FDecl (Bridge.Dialect c g) :=
  { params := ["success", "lhs_mptr", "rhs_mptr"], rets := ["ret"],
    body := helperBody R.consts (GenAst.emitEcPairingAt R.pv) }

/-- **THE SCOPE LOOKUP, BY KERNEL REDUCTION.** -/
theorem ecPairing_lookup (R : Render p G₁ G₂ Gₜ) :
    lookupFun (R.scope c g) "ec_pairing" = some (ecPairingDecl R c g, R.scope c g) := by
  kernel_rfl

/-- **THE EXPLICIT BODY.** The inlined body is the list `ecPairingBody`; `kernel_rfl` closes it
    without the elaborator's whnf sweep over the preceding helper bodies. -/
theorem ecPairing_body_eq (R : Render p G₁ G₂ Gₜ) :
    helperBody R.consts (GenAst.emitEcPairingAt R.pv) =
      ecPairingBody R.consts (GenAst.pairingScratchOf R.pv)
        templateConstantsDefault.eip2537.pairingAddress
        templateConstantsDefault.pairingTwoPairBytes templateConstantsDefault.wordBytes := by
  kernel_rfl

/-- The explicit declaration at the body above. -/
theorem ecPairingDecl_eq (R : Render p G₁ G₂ Gₜ) :
    ecPairingDecl R c g =
      { params := ["success", "lhs_mptr", "rhs_mptr"], rets := ["ret"],
        body := ecPairingBody R.consts (GenAst.pairingScratchOf R.pv)
          templateConstantsDefault.eip2537.pairingAddress
          templateConstantsDefault.pairingTwoPairBytes templateConstantsDefault.wordBytes } := by
  unfold ecPairingDecl
  rw [ecPairing_body_eq]

/-- Splitting a read into two adjacent reads. -/
theorem readBytes_append (mem : Nat → UInt8) (p m n : Nat) :
    readBytes mem p (m + n) = readBytes mem p m ++ readBytes mem (p + m) n := by
  unfold readBytes
  rw [List.range_add, List.map_append]
  congr 1
  rw [List.map_map]
  show List.map (fun i => mem (p + (m + i))) (List.range n) =
    List.map (fun i => mem (p + m + i)) (List.range n)
  apply List.map_eq_map_iff.mpr
  intro i hi
  congr 1
  omega

/-- A read outside a `copyWithin` destination is untouched. -/
theorem readBytes_copyWithin_disjoint (mem : Nat → UInt8) (dst src n p m : Nat)
    (h : dst + n ≤ p ∨ p + m ≤ dst) :
    readBytes (copyWithin mem dst src n) p m = readBytes mem p m := by
  unfold readBytes copyWithin
  refine List.map_eq_map_iff.mpr ?_
  intro i hi
  have hi' : i < m := List.mem_range.mp hi
  rw [if_neg]
  rcases h with h | h <;> omega

/-- A read whose window lies inside a `copyWithin` destination is the source slice. -/
theorem readBytes_copyWithin_window (mem : Nat → UInt8) (dst src n p m : Nat)
    (h1 : dst ≤ p) (h2 : p + m ≤ dst + n) :
    readBytes (copyWithin mem dst src n) p m = readBytes mem (src + (p - dst)) m := by
  unfold readBytes copyWithin
  refine List.map_eq_map_iff.mpr ?_
  intro i hi
  have hi' : i < m := List.mem_range.mp hi
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- The body with the five interpolated constants as explicit literals (the shape `wp_run` can
    execute). -/
def ecPairingBodyLit (scratch g2 neg gas addr frameBytes outBytes errPre errProof : Nat) :
    Block EVM.Op :=
  [ Stmt.assign ["ret"] (Expr.var "success"),
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
       Expr.lit (.number neg), Expr.lit (.number 0x100)]),
    Stmt.assign ["ret"] (Expr.builtin Op.staticcall
      [Expr.lit (.number gas), Expr.lit (.number addr),
       Expr.var "scratch", Expr.lit (.number frameBytes),
       Expr.var "scratch", Expr.lit (.number outBytes)]),
    Stmt.assign ["ret"] (Expr.builtin Op.and
      [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.returndatasize [], Expr.lit (.number outBytes)]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
      [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errPre)])],
    Stmt.assign ["ret"] (Expr.builtin Op.and
      [Expr.var "ret", Expr.builtin Op.eq
        [Expr.builtin Op.mload [Expr.var "scratch"], Expr.lit (.number 1)]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"])
      [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errProof)])],
    Stmt.assign ["ret"] (Expr.lit (.number 1)) ]

/-- The body equation at an arbitrary literal instantiation. -/
theorem ecPairingBody_eq_lit (consts : Inline.Consts) (scratch addr frameBytes outBytes
    g2 neg gas errPre errProof : Nat)
    (hG2 : ecVal consts "G2_BASE_MPTR" = Expr.lit (.number g2))
    (hNeg : ecVal consts "NEG_S_G2_BASE_MPTR" = Expr.lit (.number neg))
    (hGas : ecVal consts "PAIRING_GAS_2PAIR" = Expr.lit (.number gas))
    (hErrPre : ecVal consts "ERR_PRECOMPILE_FAILED" = Expr.lit (.number errPre))
    (hErrProof : ecVal consts "ERR_PROOF_REJECTED" = Expr.lit (.number errProof)) :
    ecPairingBody consts scratch addr frameBytes outBytes =
      ecPairingBodyLit scratch g2 neg gas addr frameBytes outBytes errPre errProof := by
  unfold ecPairingBody ecPairingBodyLit
  rw [hG2, hNeg, hGas, hErrPre, hErrProof]

/-- **THE HELPER'S RUN SHAPE AT `success = 1`.** From the helper's own environment (its three
    parameters, `ret` zeroed by the call rule), every run either reverts or exits normally with
    `ret = 1`. This is the word fact the slice's assignment reads; the product/answer refinement
    is `ec_pairing_sem`'s job. Proved by `wp_run` with the `fail` summary. -/
theorem ecPairingBodyLit_runs (funs : FunEnv (Bridge.Dialect c g)) (st : EvmState)
    (hfail : ∃ cenv, lookupFun funs "fail" = some (TraceReturn.failFDecl, cenv))
    (lhs rhs : U256) (scratch g2 neg gas addr frameBytes outBytes errPre errProof : Nat) :
    AllRuns funs [("ret", (0 : U256)), ("success", (1 : U256)),
      ("lhs_mptr", lhs), ("rhs_mptr", rhs)] st
      (ecPairingBodyLit scratch g2 neg gas addr frameBytes outBytes errPre errProof)
      (fun V' st' o => Hold (
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "ret" = some (1 : U256)))) := by
  obtain ⟨cenv, hc⟩ := hfail
  refine VKP.allRuns_of_wp_fail 100 ?_
  wp_run
  all_goals
    first
    | exact ⟨cenv, by change lookupFun funs "fail" = some (TraceReturn.failFDecl, cenv); exact hc⟩
    | (refine Hold.intro ?_
       first
       | exact Or.inl ⟨rfl, by assumption⟩
       | exact Or.inr ⟨rfl, rfl⟩)

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairing_lookup
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairing_body_eq
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit_runs
  [propext, Classical.choice, Quot.sound] native []


/-- **THE FOUR `mcopy`s AS ONE READ.** The helper lays out the frame at `dst` in four gapless
    copies; if each source lies outside `[dst, dst+768)` then the 768-byte read is the four source
    slices. The proof names the four intermediate memories, so the kernel never has to normalise
    the whole nested `copyWithin` chain at once. -/
theorem readBytes_four_copyWithin (mem : Nat → UInt8) (dst s1 s2 s3 s4 : Nat)
    (_h1 : dst + 768 ≤ s1 ∨ s1 + 128 ≤ dst)
    (h2 : dst + 768 ≤ s2 ∨ s2 + 256 ≤ dst)
    (h3 : dst + 768 ≤ s3 ∨ s3 + 128 ≤ dst)
    (h4 : dst + 768 ≤ s4 ∨ s4 + 256 ≤ dst) :
    readBytes
      (copyWithin
        (copyWithin
          (copyWithin
            (copyWithin mem dst s1 128) (dst + 128) s2 256)
          (dst + 384) s3 128)
        (dst + 512) s4 256) dst 768
      = readBytes mem s1 128 ++ (readBytes mem s2 256 ++
          (readBytes mem s3 128 ++ readBytes mem s4 256)) := by
  set m0 : Nat → UInt8 := mem
  set m1 : Nat → UInt8 := copyWithin m0 dst s1 128
  set m2 : Nat → UInt8 := copyWithin m1 (dst + 128) s2 256
  set m3 : Nat → UInt8 := copyWithin m2 (dst + 384) s3 128
  set m4 : Nat → UInt8 := copyWithin m3 (dst + 512) s4 256
  change readBytes m4 dst 768 = _
  rw [show 768 = 128 + (256 + (128 + 256)) by omega]
  rw [readBytes_append]
  rw [readBytes_append]
  rw [readBytes_append]
  have hw1 : readBytes m4 dst 128 = readBytes m0 s1 128 := by
    rw [show m4 = copyWithin m3 (dst + 512) s4 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m3 = copyWithin m2 (dst + 384) s3 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m2 = copyWithin m1 (dst + 128) s2 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m1 = copyWithin m0 dst s1 128 from rfl]
    rw [readBytes_copyWithin_window _ _ _ _ _ _ (by omega) (by omega)]
    simp
  rw [hw1]
  have hw2 : readBytes m4 (dst + 128) 256 = readBytes m0 s2 256 := by
    rw [show m4 = copyWithin m3 (dst + 512) s4 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m3 = copyWithin m2 (dst + 384) s3 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m2 = copyWithin m1 (dst + 128) s2 256 from rfl]
    rw [readBytes_copyWithin_window _ _ _ _ _ _ (by omega) (by omega)]
    rw [show m1 = copyWithin m0 dst s1 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h2 with h|h <;> omega)]
    simp
  rw [hw2]
  have hw3 : readBytes m4 (dst + 384) 128 = readBytes m0 s3 128 := by
    rw [show m4 = copyWithin m3 (dst + 512) s4 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (Or.inr (by omega))]
    rw [show m3 = copyWithin m2 (dst + 384) s3 128 from rfl]
    rw [readBytes_copyWithin_window _ _ _ _ _ _ (by omega) (by omega)]
    rw [show m2 = copyWithin m1 (dst + 128) s2 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h3 with h|h <;> omega)]
    rw [show m1 = copyWithin m0 dst s1 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h3 with h|h <;> omega)]
    simp
  rw [hw3]
  have hw4 : readBytes m4 (dst + 512) 256 = readBytes m0 s4 256 := by
    rw [show m4 = copyWithin m3 (dst + 512) s4 256 from rfl]
    rw [readBytes_copyWithin_window _ _ _ _ _ _ (by omega) (by omega)]
    rw [show m3 = copyWithin m2 (dst + 384) s3 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h4 with h|h <;> omega)]
    rw [show m2 = copyWithin m1 (dst + 128) s2 256 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h4 with h|h <;> omega)]
    rw [show m1 = copyWithin m0 dst s1 128 from rfl]
    rw [readBytes_copyWithin_disjoint _ _ _ _ _ _ (by rcases h4 with h|h <;> omega)]
    simp
  rw [hw4]

/-- The `bytesAt` face of the four-copy lemma. -/
theorem bytesAt_four_copyWithin (st : EvmState) (dst s1 s2 s3 s4 : Nat)
    (h1 : dst + 768 ≤ s1 ∨ s1 + 128 ≤ dst)
    (h2 : dst + 768 ≤ s2 ∨ s2 + 256 ≤ dst)
    (h3 : dst + 768 ≤ s3 ∨ s3 + 128 ≤ dst)
    (h4 : dst + 768 ≤ s4 ∨ s4 + 256 ≤ dst) :
    bytesAt ({ st with memory := (copyWithin
        (copyWithin
          (copyWithin
            (copyWithin st.memory dst s1 128) (dst + 128) s2 256)
          (dst + 384) s3 128)
        (dst + 512) s4 256) } : EvmState) dst 768
      = bytesAt st s1 128 ++ (bytesAt st s2 256 ++
          (bytesAt st s3 128 ++ bytesAt st s4 256)) := by
  show ByteArray.mk (readBytes
      (copyWithin
        (copyWithin
          (copyWithin
            (copyWithin st.memory dst s1 128) (dst + 128) s2 256)
          (dst + 384) s3 128)
        (dst + 512) s4 256) dst 768).toArray = _
  rw [readBytes_four_copyWithin st.memory dst s1 s2 s3 s4 h1 h2 h3 h4]
  rfl

/-- `bytesAppend` is associative (the pairing frame's fold is left-nested, a four-read is
    right-nested; this is the bridge). -/
theorem bytesAppend_assoc (a b c : Bytes) :
    bytesAppend (bytesAppend a b) c = bytesAppend a (bytesAppend b c) := by
  apply ByteArray.ext
  simp [bytesAppend, List.append_assoc]

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.readBytes_four_copyWithin
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.bytesAt_four_copyWithin
  [propext, Classical.choice, Quot.sound] native []


/-! ## The honest staticcall answer at 0x0f -/

/-- `honestRelations`'s `find?` at the pairing address is the pairing relation. -/
theorem find_pairing (product : PairingProduct) (req : YulSemantics.EVM.CallRequest)
    (htarget : req.target = pairingAddress) :
    (honestRelations product).find? (fun r => hits r req) = some (pairingRelation product) := by
  unfold honestRelations
  simp only [hits]
  rw [htarget]
  rfl

/-- A successful `pairingRelation.respond` is the answer word, and its input is valid. -/
theorem pairingRelation_respond_some (product : PairingProduct)
    (req : YulSemantics.EVM.CallRequest) (o : Midfall.Yul.CallOutcome)
    (htarget : req.target = pairingAddress)
    (h : (pairingRelation product).respond (toYulReq req) = some o) :
    pairingValidInput (ByteArray.mk req.input.toArray) = true ∧ o.success = true ∧
      o.returndata = pairingOutputWord (product (ByteArray.mk req.input.toArray)) := by
  unfold ExternalCallRelation.respond at h
  simp only [toYulReq, pairingRelation] at h
  simp only [htarget] at h
  simp only [bne_self_eq_false, Bool.false_or] at h
  by_cases hv : pairingValidInput (ByteArray.mk req.input.toArray) = true
  · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false] at h
    simp only [pairingOutput, hv, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨hv, rfl, rfl⟩
  · simp only [hv, Bool.not_false, Bool.true_or, Bool.false_eq_true, ite_true] at h
    cases h

/-- **THE HONEST RESPONSE AT 0x0f IS THE PAIRING ANSWER.** From `honestOf` at the pairing address
    and a successful response, the return word is `pairingOutputWord`, and the input is valid. -/
theorem honestOf_pairing (product : PairingProduct) (req : YulSemantics.EVM.CallRequest)
    (st : EvmState) (resp : EVM.CallResponse) (htarget : req.target = pairingAddress)
    (hsucc : resp.success = true)
    (h : honestOf (honestRelations product) req st = some resp) :
    ∃ o : Midfall.Yul.CallOutcome, resp = ofOutcome st o ∧ o.success = true ∧
      o.returndata = pairingOutputWord (product (ByteArray.mk req.input.toArray)) := by
  have hfind := find_pairing product req htarget
  unfold honestOf at h
  rw [hfind] at h
  simp only [Option.map, Option.some.injEq] at h
  by_cases hv : pairingValidInput (ByteArray.mk req.input.toArray) = true
  · have hresp : (pairingRelation product).respond (toYulReq req) =
        some { success := true, returndata := (pairingOutputWord
          (product (ByteArray.mk req.input.toArray))) } := by
      unfold ExternalCallRelation.respond
      simp only [toYulReq, pairingRelation]
      simp only [htarget]
      simp only [bne_self_eq_false, Bool.false_or, hv, Bool.not_true, Bool.false_eq_true,
        ite_false, pairingOutput, ↓reduceIte]
    rw [hresp] at h
    subst h
    exact ⟨_, rfl, rfl, rfl⟩
  · have hnone : (pairingRelation product).respond (toYulReq req) = none := by
      unfold ExternalCallRelation.respond
      simp only [toYulReq, pairingRelation]
      simp only [htarget]
      simp only [bne_self_eq_false, Bool.false_or, hv, Bool.not_false, Bool.true_or,
        Bool.false_eq_true, ite_true, pairingOutput, ↓reduceIte]
    rw [hnone] at h
    simp only [failResp] at h
    rw [← h] at hsucc
    simp at hsucc

/-- The answer word read at offset zero. -/
theorem wordFrom_pairingOutputWord (b : Bool) :
    wordFrom (pairingOutputWord b).data.toList 0 = (if b then 1 else 0) := by
  cases b <;> decide

/-- **THE PRODUCT FROM A SUCCESSFUL HONEST STATICCALL.** This is T.4's remaining semantic step:
    a successful `permissive (callsOf product)` response at 0x0f, whose 32-byte return word is 1,
    forces `product input = true`. -/
theorem product_of_honest_staticcall (product : PairingProduct)
    {req : YulSemantics.EVM.CallRequest} {st4 : EvmState} (resp : EVM.CallResponse)
    (input : Bytes)
    (hcall : (permissive (callsOf product)).Call req st4 resp)
    (htarget : req.target = pairingAddress)
    (hsucc : resp.success = true)
    (hinput : ByteArray.mk req.input.toArray = input)
    (hword : wordFrom resp.returndata 0 = 1) :
    product input = true := by
  have hc : (callsOf product).Call req st4 resp := hcall.2 hsucc
  simp only [callsOf, honestCalls] at hc
  rcases hc with hgraph | ⟨_, hfalse⟩
  · obtain ⟨o, hresp, _hsucc_o, hout⟩ :=
      honestOf_pairing product req st4 resp htarget hsucc hgraph
    subst hresp
    simp only [ofOutcome] at hword hout
    rw [hout, hinput] at hword
    rw [wordFrom_pairingOutputWord] at hword
    by_cases hb : product input = true
    · exact hb
    · simp [hb] at hword
  · cases hfalse

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.pairingRelation_respond_some
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.honestOf_pairing
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.wordFrom_pairingOutputWord
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.product_of_honest_staticcall
  [propext, Classical.choice, Quot.sound] native []


/-- `iszero (resp.flag &&& b2w (decide (len = 32))) = 0` forces a successful response. -/
theorem success_of_flag_guard {resp : EVM.CallResponse} {len : Nat}
    (h : b2w (decide ((resp.flag &&& b2w (decide (len = 32))) = 0)) = (0 : U256)) :
    resp.success = true := by
  cases hs : resp.success with
  | true => rfl
  | false => simp [CallResponse.flag, hs, b2w] at h

/-- `iszero (1 &&& b2w (decide (m = 1))) = 0` forces `m = 1`. -/
theorem load_of_and_guard {x m : U256} (hx : x = 1)
    (h : b2w (decide ((x &&& b2w (decide (m = 1))) = 0)) = (0 : U256)) : m = 1 := by
  subst hx
  by_cases hm : m = 1
  · exact hm
  · have hb : b2w (decide (m = 1)) = (0 : U256) := by
      rw [decide_eq_false hm]; rfl
    rw [hb] at h
    simp [b2w] at h

/-- The two-pair frame as the explicit left-nested append. -/
theorem pairingFrame_two (a b c d : Bytes) :
    pairingFrame [(a, b), (c, d)] =
      bytesAppend (bytesAppend (bytesAppend a b) c) d := by
  simp [pairingFrame, bytesAppend, Bytes.empty]

/-- The four-read order (`a ++ (b ++ (c ++ d))`) is the frame's left-nested order. -/
theorem bytesAppend_four_left (a b c d : Bytes) :
    bytesAppend a (bytesAppend b (bytesAppend c d)) =
      bytesAppend (bytesAppend (bytesAppend a b) c) d := by
  rw [bytesAppend_assoc, bytesAppend_assoc]

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.success_of_flag_guard
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.load_of_and_guard
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.pairingFrame_two
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.bytesAppend_four_left
  [propext, Classical.choice, Quot.sound] native []


/-- A `BitVec.ofNat 256` equality to 32 gives the Nat lower bound needed by the return read. -/
theorem length_ge_of_bitvec_ofNat_eq {n : Nat}
    (h : BitVec.ofNat 256 n = BitVec.ofNat 256 32) : 32 ≤ n := by
  have h' := congrArg BitVec.toNat h
  simp [BitVec.toNat_ofNat] at h'
  have hle := Nat.mod_le n (2 ^ 256)
  omega

/-- The first `iszero` guard's BitVec length equality gives `32 ≤ returndata.length`. -/
theorem length_ge_of_flag_guard_bv {resp : EVM.CallResponse} {n : Nat}
    (h : b2w (decide ((resp.flag &&& b2w (decide (BitVec.ofNat 256 n = BitVec.ofNat 256 32))) = 0)) =
      (0 : U256)) : 32 ≤ n := by
  by_cases heq : BitVec.ofNat 256 n = BitVec.ofNat 256 32
  · exact length_ge_of_bitvec_ofNat_eq heq
  · have hb : b2w (decide (BitVec.ofNat 256 n = BitVec.ofNat 256 32)) = (0 : U256) := by
      rw [decide_eq_false heq]; rfl
    rw [hb] at h
    simp [b2w] at h

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.length_ge_of_bitvec_ofNat_eq
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.length_ge_of_flag_guard_bv
  [propext, Classical.choice, Quot.sound] native []


/-- A bit-AND of two `0/1` words is `1` exactly when it is nonzero. -/
theorem and_eq_one_of_ne_zero {a b : U256} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : a &&& b ≠ 0) : a &&& b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.and_eq_one_of_ne_zero
  [propext, Classical.choice, Quot.sound] native []


/-- The second `and` result in the emitter's own pair form is `1`, from the BitVec guard. -/
theorem hv1_eq_of_hand {c : ExternalCalls} {g : ExternalGas} {hvflag : U256} {len : Nat}
    (hand : hvflag &&& b2w (decide (BitVec.ofNat 256 len = BitVec.ofNat 256 32)) = (1 : U256)) :
    (("ret", (hvflag &&& b2w (decide (BitVec.ofNat 256 len =
      (Bridge.Dialect c g).litValue (Literal.number 32))))).2 : U256) = 1 := by
  have hlit : (Bridge.Dialect c g).litValue (Literal.number 32) = (32 : U256) := wlit_val 32
  rw [hlit]
  change hvflag &&& b2w (decide (BitVec.ofNat 256 len = 32)) = 1
  exact hand

/-- The four-copy read at an abstract `mem4`, given the defining equation. -/
theorem readBytes_mem4_eq (mem4 : Nat → UInt8) (base : Nat → UInt8) (dst s1 s2 s3 s4 : Nat)
    (hmem4 : mem4 = copyWithin
      (copyWithin
        (copyWithin
          (copyWithin base dst s1 128) (dst + 128) s2 256)
        (dst + 384) s3 128)
      (dst + 512) s4 256)
    (h1 : dst + 768 ≤ s1 ∨ s1 + 128 ≤ dst)
    (h2 : dst + 768 ≤ s2 ∨ s2 + 256 ≤ dst)
    (h3 : dst + 768 ≤ s3 ∨ s3 + 128 ≤ dst)
    (h4 : dst + 768 ≤ s4 ∨ s4 + 256 ≤ dst) :
    readBytes mem4 dst 768 =
      readBytes base s1 128 ++ (readBytes base s2 256 ++
        (readBytes base s3 128 ++ readBytes base s4 256)) := by
  rw [hmem4]
  exact readBytes_four_copyWithin base dst s1 s2 s3 s4 h1 h2 h3 h4

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.hv1_eq_of_hand
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.readBytes_mem4_eq
  [propext, Classical.choice, Quot.sound] native []


/-! ## Emitter-form guard helpers (the opaque `hv1`/`hv2` locals) -/

def hv1Of {c : ExternalCalls} {g : ExternalGas} (resp : EVM.CallResponse) : U256 :=
  ("ret", (resp.flag &&& b2w (decide (BitVec.ofNat 256 resp.returndata.length =
    (Bridge.Dialect c g).litValue (Literal.number 32))))).2

def hv2Of {c : ExternalCalls} {g : ExternalGas} (resp : EVM.CallResponse)
    (st : EvmState) (scratch : Nat) : U256 :=
  ("ret", (hv1Of (c := c) (g := g) resp &&& b2w (decide (loadWord st.memory scratch =
    (Bridge.Dialect c g).litValue (Literal.number 1))))).2

theorem success_of_hv1Of_guard {c : ExternalCalls} {g : ExternalGas}
    {resp : EVM.CallResponse} (hv1 : U256)
    (hdef : hv1 = hv1Of (c := c) (g := g) resp)
    (h : b2w (decide (hv1 = 0)) = (Bridge.Dialect c g).zero) :
    resp.success = true := by
  rw [hdef] at h
  unfold hv1Of at h
  have h32 : (Bridge.Dialect c g).litValue (Literal.number 32) = (32 : U256) := wlit_val 32
  have hz : (Bridge.Dialect c g).zero = (0 : U256) := by
    show (Bridge.Dialect c g).litValue (Literal.number 0) = 0
    exact wlit_val 0
  rw [h32, hz] at h
  exact success_of_flag_guard h

theorem length_ge_of_hv1Of_guard {c : ExternalCalls} {g : ExternalGas}
    {resp : EVM.CallResponse} (hv1 : U256)
    (hdef : hv1 = hv1Of (c := c) (g := g) resp)
    (h : b2w (decide (hv1 = 0)) = (Bridge.Dialect c g).zero) :
    32 ≤ resp.returndata.length := by
  rw [hdef] at h
  unfold hv1Of at h
  have h32 : (Bridge.Dialect c g).litValue (Literal.number 32) = (32 : U256) := wlit_val 32
  have hz : (Bridge.Dialect c g).zero = (0 : U256) := by
    show (Bridge.Dialect c g).litValue (Literal.number 0) = 0
    exact wlit_val 0
  rw [h32, hz] at h
  exact length_ge_of_flag_guard_bv h

theorem hv1_eq_of_hv1Of_guard {c : ExternalCalls} {g : ExternalGas}
    {resp : EVM.CallResponse} (hv1 : U256)
    (hdef : hv1 = hv1Of (c := c) (g := g) resp)
    (h : b2w (decide (hv1 = 0)) = (Bridge.Dialect c g).zero) :
    hv1Of (c := c) (g := g) resp = 1 := by
  have h32 : (Bridge.Dialect c g).litValue (Literal.number 32) = (32 : U256) := wlit_val 32
  have hz : (Bridge.Dialect c g).zero = (0 : U256) := by
    show (Bridge.Dialect c g).litValue (Literal.number 0) = 0
    exact wlit_val 0
  have hv1_ne : hv1 ≠ 0 := by
    intro h0
    rw [h0] at h
    simp [b2w, hz] at h
  have hv1_ne' : (resp.flag &&& b2w (decide (BitVec.ofNat 256 resp.returndata.length =
      BitVec.ofNat 256 32))) ≠ 0 := by
    intro h0
    have hzero : hv1 = 0 := by
      rw [hdef]
      change (resp.flag &&& b2w (decide (BitVec.ofNat 256 resp.returndata.length =
        (Bridge.Dialect c g).litValue (Literal.number 32)))) = 0
      rw [h32]
      exact h0
    exact hv1_ne hzero
  have hflagbit : resp.flag = 0 ∨ resp.flag = 1 := by
    cases resp.success <;> simp [CallResponse.flag]
  have hlenbit : b2w (decide (BitVec.ofNat 256 resp.returndata.length = BitVec.ofNat 256 32)) = 0 ∨
      b2w (decide (BitVec.ofNat 256 resp.returndata.length = BitVec.ofNat 256 32)) = 1 := by
    by_cases heq : BitVec.ofNat 256 resp.returndata.length = BitVec.ofNat 256 32
    · right; simp [heq, b2w]
    · left; simp [decide_eq_false heq, b2w]
  have hand := and_eq_one_of_ne_zero hflagbit hlenbit hv1_ne'
  simpa [hv1Of] using hv1_eq_of_hand (c := c) (g := g)
    (len := resp.returndata.length) hand

theorem load_of_hv2Of_guard {c : ExternalCalls} {g : ExternalGas}
    {resp : EVM.CallResponse} {st : EvmState} {scratch : Nat} (hv2 : U256)
    (hdef : hv2 = hv2Of (c := c) (g := g) resp st scratch)
    (h : b2w (decide (hv2 = 0)) = (Bridge.Dialect c g).zero)
    (hv1eq : hv1Of (c := c) (g := g) resp = 1) :
    loadWord st.memory scratch = 1 := by
  rw [hdef] at h
  unfold hv2Of at h
  have h1 : (Bridge.Dialect c g).litValue (Literal.number 1) = (1 : U256) := wlit_val 1
  have hz : (Bridge.Dialect c g).zero = (0 : U256) := by
    show (Bridge.Dialect c g).litValue (Literal.number 0) = 0
    exact wlit_val 0
  rw [h1, hz] at h
  exact load_of_and_guard hv1eq h

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.success_of_hv1Of_guard
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.length_ge_of_hv1Of_guard
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.hv1_eq_of_hv1Of_guard
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.load_of_hv2Of_guard
  [propext, Classical.choice, Quot.sound] native []


/-- **THE NORMAL LEAF, PRODUCT PART.** All the guard work is in the four helpers above; this
    lemma is the assembly T.4 needs. `hinput` is the four-copy frame identification. -/
theorem ecPairing_normal_product (product : PairingProduct)
    {c : ExternalCalls} {g : ExternalGas}
    {req : YulSemantics.EVM.CallRequest} {st4 st5 : EvmState}
    (resp : EVM.CallResponse) (LA GB LB GN : Bytes) (scratchW : U256)
    (hcall : (permissive (callsOf product)).Call req st4 resp)
    (htarget : req.target = pairingAddress)
    (hguard1 : b2w (decide (hv1Of (c := c) (g := g) resp = 0)) = (Bridge.Dialect c g).zero)
    (hguard2 : b2w (decide (hv2Of (c := c) (g := g) resp st5 scratchW.toNat = 0)) = (Bridge.Dialect c g).zero)
    (hst5 : st5.memory = copyReturn st4.memory scratchW.toNat 32 resp.returndata)
    (hinput : ByteArray.mk req.input.toArray = pairingFrame [(LA, GB), (LB, GN)]) :
    product (pairingFrame [(LA, GB), (LB, GN)]) = true := by
  have hsucc : resp.success = true :=
    success_of_hv1Of_guard (hv1 := hv1Of (c := c) (g := g) resp) rfl hguard1
  have hlen : 32 ≤ resp.returndata.length :=
    length_ge_of_hv1Of_guard (hv1 := hv1Of (c := c) (g := g) resp) rfl hguard1
  have hv1eq : hv1Of (c := c) (g := g) resp = 1 :=
    hv1_eq_of_hv1Of_guard (hv1 := hv1Of (c := c) (g := g) resp) rfl hguard1
  have hload : loadWord st5.memory scratchW.toNat = 1 :=
    load_of_hv2Of_guard (hv2 := hv2Of (c := c) (g := g) resp st5 scratchW.toNat) rfl hguard2 hv1eq
  have hword : wordFrom resp.returndata 0 = 1 := by
    have hcopy : loadWord st5.memory scratchW.toNat = wordFrom resp.returndata 0 := by
      rw [hst5]
      rw [Midfall.Yul.Word.loadWord_copyReturn (dst := scratchW.toNat) (size := 32) (q := scratchW.toNat)
        (h := by
          constructor
          · omega
          · rw [Nat.min_eq_left hlen])]
      simp
    rw [hcopy] at hload
    exact hload
  exact product_of_honest_staticcall (product := product) (resp := resp)
    (input := pairingFrame [(LA, GB), (LB, GN)]) (hcall := hcall) (htarget := htarget)
    (hsucc := hsucc) (hinput := hinput) (hword := hword)

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairing_normal_product
  [propext, Classical.choice, Quot.sound] native []

/-! ## The helper's normal run: trimming the `success = 1` guard and the product leaf -/

theorem iszero_ret_one_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {r : EResult (Bridge.Dialect c g)}
    (hret : VEnv.get V "ret" = some (1 : U256))
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var "ret"]) r) : r = .vals [0] st := by
  cases h with
  | builtinOk hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget =>
                  simp_all [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w]
                  exact hbi.1.symm
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var hget => simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h => cases h

theorem iszero_ret_one_ne_halts {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st st₂ : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var "ret"]) (.halt st₂)) : False := by
  cases h with
  | builtinHalt hargs hbi =>
      cases hargs with
      | argsCons hnil hvar =>
          cases hnil with
          | argsNil =>
              cases hvar with
              | var _ => simp [Bridge.Dialect, builtinWithExternal, stepOp, un, b2w] at hbi
  | builtinArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h => cases h
      | argsHeadHalt _ h => cases h

theorem cond_ret_one_skip {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {body : Block EVM.Op} {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome}
    (hret : VEnv.get V "ret" = some (1 : U256))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) body) V' st' o) :
    V' = V ∧ st' = st ∧ o = .normal := by
  cases h with
  | ifTrue hc hnz _ =>
      have h0 := iszero_ret_one_val hret hc
      cases h0
      exact absurd rfl hnz
  | ifFalse hc _ =>
      have h0 := iszero_ret_one_val hret hc
      cases h0
      exact ⟨rfl, rfl, rfl⟩
  | ifHalt hc => exact (iszero_ret_one_ne_halts hc).elim

theorem assign_ret_success {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.assign ["ret"] (Expr.var "success")) V' st' o) :
    V' = VEnv.set V "ret" 1 ∧ st' = st ∧ o = .normal := by
  cases h with
  | assignVal hex hlen =>
      cases hex with
      | var hget =>
          simp only [VEnv.get] at hsucc hget
          rw [hsucc] at hget
          cases hget
          exact ⟨rfl, rfl, rfl⟩
  | assignHalt hex => cases hex

theorem venv_get_set_same {V : VEnv (Bridge.Dialect c g)} {x : Ident} {v w : U256}
    (h : VEnv.get V x = some w) : VEnv.get (VEnv.set V x v) x = some v := by
  induction V with
  | nil => cases h
  | cons p rest ih =>
      obtain ⟨y, u⟩ := p
      by_cases hy : y = x
      · subst hy
        simp [VEnv.set, VEnv.get]
      · have hget : VEnv.get rest x = some w := by
          have h2 : VEnv.get ((y, u) :: rest) x = some w := h
          simpa [VEnv.get, List.find?, hy] using h2
        have h3 := ih hget
        simpa [VEnv.set, VEnv.get, List.find?, hy] using h3

theorem ecPairing_trim_exec (funs : FunEnv (Bridge.Dialect c g)) (V : VEnv (Bridge.Dialect c g))
    (st : EvmState) (rest : Block EVM.Op) {V' : VEnv (Bridge.Dialect c g)}
    {st' : EvmState} {o : Outcome} {w : U256}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hbound : VEnv.get V "ret" = some w)
    (h : ExecStmts (Bridge.Dialect c g) funs V st
      (Stmt.assign ["ret"] (Expr.var "success") ::
        Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) [Stmt.leave] :: rest) V' st' o) :
    ExecStmts (Bridge.Dialect c g) funs (VEnv.set V "ret" 1) st rest V' st' o := by
  rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) h with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · obtain ⟨hV, hst, -⟩ := assign_ret_success hsucc h₁
    subst hV; subst hst
    have hret1 : VEnv.get (VEnv.set V "ret" 1) "ret" = some (1 : U256) :=
      venv_get_set_same hbound
    rcases Step.stmts_cons_inv (D := Bridge.Dialect c g) hrest with ⟨V₂, st₂, h₂, hrest₂⟩ | ⟨h₂, hne₂⟩
    · obtain ⟨hV2, hst2, -⟩ := cond_ret_one_skip hret1 h₂
      subst hV2; subst hst2
      exact hrest₂
    · obtain ⟨-, -, ho⟩ := cond_ret_one_skip hret1 h₂
      exact absurd ho hne₂
  · obtain ⟨-, -, ho⟩ := assign_ret_success hsucc h₁
    exact absurd ho hne

theorem ecPairingBodyLit_trim {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {rest : Block EVM.Op} {Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop}
    {w : U256}
    (hsucc : VEnv.get V "success" = some (1 : U256))
    (hbound : VEnv.get V "ret" = some w) :
    AllRuns funs (VEnv.set V "ret" 1) st rest Q →
    AllRuns funs V st
      (Stmt.assign ["ret"] (Expr.var "success") ::
        Stmt.cond (Expr.builtin Op.iszero [Expr.var "ret"]) [Stmt.leave] :: rest) Q :=
  fun h V' st' o hrun => h V' st' o (ecPairing_trim_exec funs V st rest hsucc hbound hrun)

set_option maxHeartbeats 200000 in
theorem ecPairingBodyLit_product_runs (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)) (st : EvmState)
    (hfail : ∃ cenv, lookupFun funs "fail" = some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, cenv))
    (LA GB LB GN : Bytes)
    (lhsW rhsW : U256) (scratch g2 neg : Nat) (gas errPre errProof : Nat)
    (hsrc1 : bytesAt st lhsW.toNat 128 = LA)
    (hsrc2 : bytesAt st (g2 % 2^256) 256 = GB)
    (hsrc3 : bytesAt st rhsW.toNat 128 = LB)
    (hsrc4 : bytesAt st (neg % 2^256) 256 = GN)
    (hdisj1 : (scratch % 2^256) + 768 ≤ lhsW.toNat ∨ lhsW.toNat + 128 ≤ (scratch % 2^256))
    (hdisj2 : (scratch % 2^256) + 768 ≤ (g2 % 2^256) ∨ (g2 % 2^256) + 256 ≤ (scratch % 2^256))
    (hdisj3 : (scratch % 2^256) + 768 ≤ rhsW.toNat ∨ rhsW.toNat + 128 ≤ (scratch % 2^256))
    (hdisj4 : (scratch % 2^256) + 768 ≤ (neg % 2^256) ∨ (neg % 2^256) + 256 ≤ (scratch % 2^256))
    (hg2 : g2 < 2^256) (hneg : neg < 2^256) (hscratchWin : scratch + 768 < 2^256) :
    AllRuns funs [("success", (1 : U256)), ("lhs_mptr", lhsW),
      ("rhs_mptr", rhsW), ("ret", (0 : U256))] st
      (ecPairingBodyLit scratch g2 neg gas 0x0f 768 32 errPre errProof)
      (fun V' st' o => Hold (
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "ret" = some (1 : U256) ∧
          product (pairingFrame [(LA, GB), (LB, GN)]) = true))) := by
  obtain ⟨cenv, hc⟩ := hfail
  unfold ecPairingBodyLit
  refine ecPairingBodyLit_trim (Q := fun V' st' o => Hold (
      (o = .halt ∧ Reverted st') ∨
      (o = .normal ∧ VEnv.get V' "ret" = some (1 : U256) ∧
        product (pairingFrame [(LA, GB), (LB, GN)]) = true)))
    (hsucc := rfl) (hbound := rfl) ?_
  refine allRuns_of_wp_fail 100 ?_
  wp_run
  all_goals
    first
    | exact ⟨cenv, by change lookupFun funs "fail" = some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, cenv); exact hc⟩
    | (refine Hold.intro ?_
       first
       | exact Or.inl ⟨rfl, by assumption⟩
       | (refine Or.inr ⟨rfl, ⟨?_, ?_⟩⟩
          · rfl
          · refine ecPairing_normal_product (product := product)
              (c := permissive (callsOf product)) (g := g)
              (LA := LA) (GB := GB) (LB := LB) (GN := GN)
              (hcall := by assumption) (htarget := rfl)
              (hguard1 := by assumption) (hguard2 := by assumption)
              (hst5 := rfl) (hinput := ?_)
            simp +zetaDelta only [YulSemantics.EVM.litValue, BitVec.toNat_ofNat, BitVec.toNat_add]
            have h128 : (128 : Nat) % 2^256 = 128 := by simp
            have h256 : (256 : Nat) % 2^256 = 256 := by simp
            have h768 : (768 : Nat) % 2^256 = 768 := by simp
            have hd128 : ((scratch % 2^256) + 128 % 2^256) % 2^256 = (scratch % 2^256) + 128 := by
              rw [Nat.mod_eq_of_lt (by omega : scratch < 2^256), h128]
              exact Nat.mod_eq_of_lt (by omega)
            have hd384 : ((scratch % 2^256) + 384 % 2^256) % 2^256 = (scratch % 2^256) + 384 := by
              have h384 : (384 : Nat) % 2^256 = 384 := by norm_num
              rw [Nat.mod_eq_of_lt (by omega : scratch < 2^256), h384]
              exact Nat.mod_eq_of_lt (by omega)
            have hd512 : ((scratch % 2^256) + 512 % 2^256) % 2^256 = (scratch % 2^256) + 512 := by
              have h512 : (512 : Nat) % 2^256 = 512 := by norm_num
              rw [Nat.mod_eq_of_lt (by omega : scratch < 2^256), h512]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hd128, hd384, hd512, h128, h256, h768]
            set mem4 : Nat → UInt8 := copyWithin
              (copyWithin
                (copyWithin
                  (copyWithin st.memory (scratch % 2^256) lhsW.toNat 128)
                  ((scratch % 2^256) + 128) (g2 % 2^256) 256)
                ((scratch % 2^256) + 384) rhsW.toNat 128)
              ((scratch % 2^256) + 512) (neg % 2^256) 256 with hmem4
            rw [readBytes_mem4_eq mem4 st.memory (scratch % 2^256) lhsW.toNat
              (g2 % 2^256) rhsW.toNat (neg % 2^256) hmem4 hdisj1 hdisj2 hdisj3 hdisj4]
            have hs1 : readBytes st.memory lhsW.toNat 128 = LA.data.toList := by
              have := congrArg Array.toList (congrArg ByteArray.data hsrc1)
              simpa [bytesAt] using this
            have hs2 : readBytes st.memory (g2 % 2^256) 256 = GB.data.toList := by
              have := congrArg Array.toList (congrArg ByteArray.data hsrc2)
              simpa [bytesAt] using this
            have hs3 : readBytes st.memory rhsW.toNat 128 = LB.data.toList := by
              have := congrArg Array.toList (congrArg ByteArray.data hsrc3)
              simpa [bytesAt] using this
            have hs4 : readBytes st.memory (neg % 2^256) 256 = GN.data.toList := by
              have := congrArg Array.toList (congrArg ByteArray.data hsrc4)
              simpa [bytesAt] using this
            rw [hs1, hs2, hs3, hs4]
            rw [pairingFrame_two]
            rw [← bytesAppend_four_left]
            apply ByteArray.ext
            simp [bytesAppend, List.append_assoc]
          ))

#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.iszero_ret_one_val
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.cond_ret_one_skip
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.assign_ret_success
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairing_trim_exec
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit_trim
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit_product_runs
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV2.Blocks.EcPairing

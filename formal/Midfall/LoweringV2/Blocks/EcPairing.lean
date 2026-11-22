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
    (req : YulSemantics.EVM.CallRequest) (st4 : EvmState) (resp : EVM.CallResponse)
    (input : Bytes) (htarget : req.target = pairingAddress)
    (hsucc : resp.success = true)
    (hcall : (permissive (callsOf product)).Call req st4 resp)
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

end Midfall.LoweringV2.Blocks.EcPairing

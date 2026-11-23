/-
  Midfall.LoweringV3.FpClean

  ROW.FP (WP A11) - the two G1 slot reads `Inv .pcs` pins, extracted as named
  lemmas rather than re-derived at every clean-arm use site.  The extraction is
  the same checkpoint-index reduction and chain split as `Inv_pairing_of_pcs`.
-/
import Midfall.LoweringV3.FpConsts

set_option autoImplicit false
open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

set_option maxHeartbeats 800000 in
theorem Inv_pcs_pairingLhs {calls : ExternalCalls} {gas : ExternalGas}
    {R : Render p G₁ G₂ Gₜ} {S : Snapshot p G₁ G₂ Gₜ}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S V st) :
    holdsG1 R.E st (ptrAddr R.pv.memory.pairingLhsMptr) S.c.dual.left.eval = true := by
  unfold Midfall.Lowering.Inv at h
  simp only [Midfall.Lowering.InvAt] at h
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  simp only [h15, h25, h35, h45, h55, if_true] at h
  simp only [Bool.and_eq_true] at h
  simp only [and_assoc] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  exact h32.2.1

set_option maxHeartbeats 800000 in
theorem Inv_pcs_pairingRhs {calls : ExternalCalls} {gas : ExternalGas}
    {R : Render p G₁ G₂ Gₜ} {S : Snapshot p G₁ G₂ Gₜ}
    {V : VEnv (Bridge.Dialect calls gas)} {st : EvmState}
    (h : Midfall.Lowering.Inv R.E R.params Checkpoint.pcs R.pv S V st) :
    holdsG1 R.E st (ptrAddr R.pv.memory.pairingRhsMptr) S.c.dual.right.eval = true := by
  unfold Midfall.Lowering.Inv at h
  simp only [Midfall.Lowering.InvAt] at h
  simp only [Midfall.Lowering.checkpoint_le_def, Checkpoint.idx] at h
  have h15 : (1 : Nat) ≤ 5 := by decide
  have h25 : (2 : Nat) ≤ 5 := by decide
  have h35 : (3 : Nat) ≤ 5 := by decide
  have h45 : (4 : Nat) ≤ 5 := by decide
  have h55 : (5 : Nat) ≤ 5 := by decide
  simp only [h15, h25, h35, h45, h55, if_true] at h
  simp only [Bool.and_eq_true] at h
  simp only [and_assoc] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  exact h32.2.2.1

#assert_axioms Midfall.LoweringV3.Inv_pcs_pairingLhs
  [propext, Classical.choice, Quot.sound] native []
#assert_axioms Midfall.LoweringV3.Inv_pcs_pairingRhs
  [propext, Classical.choice, Quot.sound] native []

/-! ## 2. THE CLEAN CALL CONTRACT AT A FIXED STATE

    `EcPairing.ecPairing_call_contract_lits` states exactly the clean call's post,
    but its four source-slice hypotheses are `∀ st, bytesAt st … = …`, which no
    state-dependent frame satisfies. The clean slice's source slices come from
    `Inv .pcs` and the VK payload at the boundary's OWN state, so the contract is
    restated here with `st` fixed before the slice equations. The proof is the
    same call inversion and the same `ecPairingBodyLit_product_runs`; only the
    binder order (and therefore `hsrc1` vs `hsrc1 st`) changes. -/
set_option maxHeartbeats 400000 in
theorem ecPairing_call_clean_at {g : ExternalGas} (product : PairingProduct)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    {decl : FDecl (Bridge.Dialect (permissive (callsOf product)) g)}
    {cenv cenv' : FunEnv (Bridge.Dialect (permissive (callsOf product)) g)}
    (scratch g2 neg gas errPre errProof rhsNat lhsNat : Nat)
    (LA GB LB GN : Bytes) (st : EvmState)
    (hlook : lookupFun funs "ec_pairing" = some (decl, cenv))
    (hbody : decl.body = Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
      scratch g2 neg gas 0x0f 768 32 errPre errProof)
    (hparams : decl.params = ["success", "lhs_mptr", "rhs_mptr"])
    (hrets : decl.rets = ["ret"])
    (hfail : lookupFun cenv "fail" =
      some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, cenv'))
    (hsrc1 : bytesAt st (BitVec.ofNat 256 rhsNat).toNat 128 = LA)
    (hsrc2 : bytesAt st (g2 % 2^256) 256 = GB)
    (hsrc3 : bytesAt st (BitVec.ofNat 256 lhsNat).toNat 128 = LB)
    (hsrc4 : bytesAt st (neg % 2^256) 256 = GN)
    (hdisj1 : (scratch % 2^256) + 768 ≤ (BitVec.ofNat 256 rhsNat).toNat ∨
      (BitVec.ofNat 256 rhsNat).toNat + 128 ≤ (scratch % 2^256))
    (hdisj2 : (scratch % 2^256) + 768 ≤ (g2 % 2^256) ∨ (g2 % 2^256) + 256 ≤ (scratch % 2^256))
    (hdisj3 : (scratch % 2^256) + 768 ≤ (BitVec.ofNat 256 lhsNat).toNat ∨
      (BitVec.ofNat 256 lhsNat).toNat + 128 ≤ (scratch % 2^256))
    (hdisj4 : (scratch % 2^256) + 768 ≤ (neg % 2^256) ∨ (neg % 2^256) + 256 ≤ (scratch % 2^256))
    (hg2 : g2 < 2^256) (hneg : neg < 2^256) (hscratchWin : scratch + 768 < 2^256) :
    ∀ (V : VEnv (Bridge.Dialect (permissive (callsOf product)) g))
      (r : EResult (Bridge.Dialect (permissive (callsOf product)) g)),
      VEnv.get V "success" = some (1 : U256) →
      EvalExpr (Bridge.Dialect (permissive (callsOf product)) g) funs V st
        (Expr.call "ec_pairing"
          [Expr.var "success", Expr.lit (.number rhsNat), Expr.lit (.number lhsNat)]) r →
      (∃ st', r = .vals [1] st' ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
        (∀ x, x < (scratch % 2^256) ∨ (scratch % 2^256) + 768 ≤ x →
          st'.memory x = st.memory x) ∧
        product (pairingFrame [(LA, GB), (LB, GN)]) = true) ∨
      (∃ st', r = .halt st' ∧ Reverted st') := by
  intro V r hsucc he
  have hhoist : hoist (Bridge.Dialect (permissive (callsOf product)) g)
      (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
        scratch g2 neg gas 0x0f 768 32 errPre errProof) = [] := rfl
  have hfail' : lookupFun (hoist (Bridge.Dialect (permissive (callsOf product)) g)
      (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
        scratch g2 neg gas 0x0f 768 32 errPre errProof) :: cenv) "fail" =
      some (Midfall.LoweringV2.Blocks.TraceReturn.failFDecl, cenv') := by
    rw [hhoist]; simpa [lookupFun] using hfail
  cases he with
  | callOk hargs hlook' hlen hbodyrun ho =>
      cases hargs with
      | argsCons hrest hhead3 =>
        cases hrest with
        | argsCons hrest2 hhead2 =>
          cases hrest2 with
          | argsCons hrest3 hhead1 =>
            cases hrest3 with
            | argsNil =>
              cases hhead1 with
              | lit =>
                cases hhead2 with
                | lit =>
                  cases hhead3 with
                  | var hget3 =>
                    rename_i v3
                    have hv3 : v3 = 1 :=
                      (Option.some.inj (by rw [hsucc] at hget3; exact hget3)).symm
                    rw [hlook] at hlook'
                    cases hlook'
                    rw [hparams] at hlen
                    rw [hparams, hrets, hbody] at hbodyrun
                    cases hbodyrun with
                    | block hstmts =>
                      rw [hv3] at hstmts
                      simp only [Bridge.Dialect, YulSemantics.EVM.litValue] at hstmts
                      have hbodyC :=
                        Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit_product_runs
                        (c := permissive (callsOf product))
                        (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
                            scratch g2 neg gas 0x0f 768 32 errPre errProof) :: cenv)
                        (st := st) (hfail := ⟨cenv', hfail'⟩) (product := product)
                        (LA := LA) (GB := GB) (LB := LB) (GN := GN)
                        (lhsW := BitVec.ofNat 256 rhsNat)
                        (rhsW := BitVec.ofNat 256 lhsNat) (scratch := scratch)
                        (g2 := g2) (neg := neg) (gas := gas)
                        (errPre := errPre) (errProof := errProof)
                        (hsrc1 := hsrc1) (hsrc2 := hsrc2) (hsrc3 := hsrc3)
                        (hsrc4 := hsrc4) (hdisj1 := hdisj1) (hdisj2 := hdisj2)
                        (hdisj3 := hdisj3) (hdisj4 := hdisj4) (hg2 := hg2)
                        (hneg := hneg) (hscratchWin := hscratchWin)
                      have hpost := hbodyC _ _ _ (by exact hstmts)
                      have hpost' := hpost.elim
                      rcases hpost' with ⟨hon, hrevBody⟩ | ⟨hoh, hret, _henv, hpres, hprod⟩
                      · rcases ho with hn | hl
                        · exact absurd (hn.symm.trans hon) (by decide)
                        · exact absurd (hl.symm.trans hon) (by decide)
                      · have houter : (["success", "lhs_mptr", "rhs_mptr"].zip
                            [1, BitVec.ofNat 256 rhsNat, BitVec.ofNat 256 lhsNat] ++
                            bindZeros (Bridge.Dialect (permissive (callsOf product)) g) ["ret"]) =
                            [("success", (1 : U256)), ("lhs_mptr", BitVec.ofNat 256 rhsNat),
                              ("rhs_mptr", BitVec.ofNat 256 lhsNat),
                              ("ret", (Bridge.Dialect (permissive (callsOf product)) g).zero)] := by
                          simp [bindZeros]
                        refine Or.inl ⟨_, ?_, _henv.1, _henv.2, hpres, hprod⟩
                        simp only [Bridge.Dialect, YulSemantics.EVM.litValue]
                        rw [hrets, hv3, houter]
                        simp only [List.map_cons, List.map_nil]
                        rw [hret]
                        rfl
  | callHalt hargs hlook' hlen hbodyrun =>
      cases hargs with
      | argsCons hrest hhead3 =>
        cases hrest with
        | argsCons hrest2 hhead2 =>
          cases hrest2 with
          | argsCons hrest3 hhead1 =>
            cases hrest3 with
            | argsNil =>
              cases hhead1 with
              | lit =>
                cases hhead2 with
                | lit =>
                  cases hhead3 with
                  | var hget3 =>
                    rename_i v3
                    have hv3 : v3 = 1 :=
                      (Option.some.inj (by rw [hsucc] at hget3; exact hget3)).symm
                    rw [hlook] at hlook'
                    cases hlook'
                    rw [hparams] at hlen
                    rw [hparams, hrets, hbody] at hbodyrun
                    cases hbodyrun with
                    | block hstmts =>
                      rw [hv3] at hstmts
                      simp only [Bridge.Dialect, YulSemantics.EVM.litValue] at hstmts
                      have hbodyC :=
                        Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit_product_runs
                        (c := permissive (callsOf product))
                        (funs := hoist (Bridge.Dialect (permissive (callsOf product)) g)
                          (Midfall.LoweringV2.Blocks.EcPairing.ecPairingBodyLit
                            scratch g2 neg gas 0x0f 768 32 errPre errProof) :: cenv)
                        (st := st) (hfail := ⟨cenv', hfail'⟩) (product := product)
                        (LA := LA) (GB := GB) (LB := LB) (GN := GN)
                        (lhsW := BitVec.ofNat 256 rhsNat)
                        (rhsW := BitVec.ofNat 256 lhsNat) (scratch := scratch)
                        (g2 := g2) (neg := neg) (gas := gas)
                        (errPre := errPre) (errProof := errProof)
                        (hsrc1 := hsrc1) (hsrc2 := hsrc2) (hsrc3 := hsrc3)
                        (hsrc4 := hsrc4) (hdisj1 := hdisj1) (hdisj2 := hdisj2)
                        (hdisj3 := hdisj3) (hdisj4 := hdisj4) (hg2 := hg2)
                        (hneg := hneg) (hscratchWin := hscratchWin)
                      have hpost := hbodyC _ _ _ (by exact hstmts)
                      have hpost' := hpost.elim
                      rcases hpost' with ⟨hon, hrevBody⟩ | ⟨hoh, hret, _henv, hpres, hprod⟩
                      · exact Or.inr ⟨_, rfl, hrevBody⟩
                      · exact absurd hoh (by decide)
  | callArgsHalt hargs =>
      cases hargs with
      | argsRestHalt h1 =>
          cases h1 with
          | argsRestHalt h2 =>
              cases h2 with
              | argsRestHalt h3 => cases h3
              | argsHeadHalt _ hhead => cases hhead
          | argsHeadHalt _ hhead => cases hhead
      | argsHeadHalt _ hhead => cases hhead

#assert_axioms Midfall.LoweringV3.ecPairing_call_clean_at
  [propext, Classical.choice, Quot.sound] native []

end Midfall.LoweringV3

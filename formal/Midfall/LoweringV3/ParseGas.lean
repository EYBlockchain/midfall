/-
  Midfall.LoweringV3.ParseGas

  The `gas()` scan over a block parsed from generator text (CERT.5, D-GATE1).

  `YulParse.parseTokens` resolves an identifier through `EVM.mkCall`: a token `"gas"`
  becomes `Expr.builtin EVM.Op.gas`, every other name is a variable or a user call.
  So a token stream that does not contain `"gas"` parses to a gas-free AST. This file
  proves that, with a fuel-monotonicity lemma for `gasFreeScan`, and exposes the two
  entry points `parseTokens_gfs`/`parseLines_gfs`.
-/
import Midfall.LoweringV3.Totality
import Midfall.Lowering.YulParse

set_option autoImplicit false
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge
open Midfall.Lowering.YulParse

namespace Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### Fuel monotonicity -/

mutual
theorem gfs_mono_e : ∀ (e : Expr EVM.Op) {n m : Nat}, n ≤ m →
    gasFreeScan n (.e e) = true → gasFreeScan m (.e e) = true
  | .lit l, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | .var x, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | .builtin op args, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨h.1, gfs_mono_es args (by omega) h.2⟩
  | .call f args, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan] at h ⊢
          exact gfs_mono_es args (by omega) h

theorem gfs_mono_es : ∀ (es : List (Expr EVM.Op)) {n m : Nat}, n ≤ m →
    gasFreeScan n (.es es) = true → gasFreeScan m (.es es) = true
  | [], n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | e :: rest, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨gfs_mono_e e (by omega) h.1, gfs_mono_es rest (by omega) h.2⟩

theorem gfs_mono_s : ∀ (s : Stmt EVM.Op) {n m : Nat}, n ≤ m →
    gasFreeScan n (.s s) = true → gasFreeScan m (.s s) = true
  | .block body, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m => simp only [gasFreeScan] at h ⊢; exact gfs_mono_b body (by omega) h
  | .funDef name params rets body, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m => simp only [gasFreeScan] at h ⊢; exact gfs_mono_b body (by omega) h
  | .letDecl vars none, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | .letDecl vars (some e), n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m => simp only [gasFreeScan] at h ⊢; exact gfs_mono_e e (by omega) h
  | .assign vars e, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m => simp only [gasFreeScan] at h ⊢; exact gfs_mono_e e (by omega) h
  | .cond c body, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨gfs_mono_e c (by omega) h.1, gfs_mono_b body (by omega) h.2⟩
  | .switch c cases dflt, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          refine ⟨⟨gfs_mono_e c (by omega) h.1.1, gfs_mono_cs cases (by omega) h.1.2⟩, ?_⟩
          cases dflt with
          | none => exact h.2
          | some d => exact gfs_mono_b d (by omega) h.2
  | .forLoop init c post body, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨⟨⟨gfs_mono_b init (by omega) h.1.1.1, gfs_mono_e c (by omega) h.1.1.2⟩,
            gfs_mono_b post (by omega) h.1.2⟩, gfs_mono_b body (by omega) h.2⟩
  | .exprStmt e, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m => simp only [gasFreeScan] at h ⊢; exact gfs_mono_e e (by omega) h
  | .break, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | .continue, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | .leave, n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]

theorem gfs_mono_b : ∀ (b : Block EVM.Op) {n m : Nat}, n ≤ m →
    gasFreeScan n (.b b) = true → gasFreeScan m (.b b) = true
  | [], n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | s :: rest, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨gfs_mono_s s (by omega) h.1, gfs_mono_b rest (by omega) h.2⟩

theorem gfs_mono_cs : ∀ (cs : List (Literal × Block EVM.Op)) {n m : Nat}, n ≤ m →
    gasFreeScan n (.cs cs) = true → gasFreeScan m (.cs cs) = true
  | [], n, m, hnm, h => by cases n <;> cases m <;> simp_all [gasFreeScan]
  | (l, b) :: rest, n, m, hnm, h => by
      cases n with
      | zero => simp [gasFreeScan] at h
      | succ n =>
        cases m with
        | zero => omega
        | succ m =>
          simp only [gasFreeScan, Bool.and_eq_true] at h ⊢
          exact ⟨gfs_mono_b b (by omega) h.1, gfs_mono_cs rest (by omega) h.2⟩
end

/-! ### Constructors -/

theorem gfs_lit (l : Literal) : GasFreeScan (.e (.lit l)) := ⟨1, by simp [gasFreeScan]⟩

theorem gfs_var (x : Ident) : GasFreeScan (.e (.var x)) := ⟨1, by simp [gasFreeScan]⟩

theorem gfs_es_nil : GasFreeScan (.es ([] : List (Expr EVM.Op))) :=
  ⟨1, by simp [gasFreeScan]⟩

theorem gfs_es_cons {e : Expr EVM.Op} {es : List (Expr EVM.Op)}
    (he : GasFreeScan (.e e)) (hes : GasFreeScan (.es es)) :
    GasFreeScan (.es (e :: es)) := by
  obtain ⟨n, hn⟩ := he
  obtain ⟨m, hm⟩ := hes
  refine ⟨max n m + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  exact ⟨gfs_mono_e e (by omega) hn, gfs_mono_es es (by omega) hm⟩

theorem gfs_builtin {op : EVM.Op} {args : List (Expr EVM.Op)}
    (hop : op ≠ EVM.Op.gas) (hargs : GasFreeScan (.es args)) :
    GasFreeScan (.e (.builtin op args)) := by
  obtain ⟨n, hn⟩ := hargs
  refine ⟨n + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  rw [Bool.not_eq_true']
  exact ⟨beq_eq_false_iff_ne.mpr hop, hn⟩

theorem gfs_call {f : Ident} {args : List (Expr EVM.Op)}
    (hargs : GasFreeScan (.es args)) : GasFreeScan (.e (.call f args)) := by
  obtain ⟨n, hn⟩ := hargs
  exact ⟨n + 1, by simp [gasFreeScan, hn]⟩

theorem parse_ne_gas {name : String} (h : name ≠ "gas") :
    EVM.parse name ≠ some EVM.Op.gas := by
  intro hg
  unfold EVM.parse at hg
  split at hg <;> simp_all

theorem gfs_mkCall {name : Ident} {args : List (Expr EVM.Op)}
    (hname : name ≠ "gas") (hargs : GasFreeScan (.es args)) :
    GasFreeScan (.e (EVM.mkCall name args)) := by
  unfold EVM.mkCall
  cases hp : EVM.parse name with
  | none => exact gfs_call hargs
  | some op =>
      refine gfs_builtin ?_ hargs
      intro hop
      subst hop
      exact parse_ne_gas hname hp


theorem gfs_b_nil : GasFreeScan (.b ([] : Block EVM.Op)) := ⟨1, by simp [gasFreeScan]⟩

theorem gfs_b_cons {s : Stmt EVM.Op} {b : Block EVM.Op}
    (hs : GasFreeScan (.s s)) (hb : GasFreeScan (.b b)) : GasFreeScan (.b (s :: b)) := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  exact ⟨gfs_mono_s s (by omega) hn, gfs_mono_b b (by omega) hm⟩

theorem gfs_cs_nil : GasFreeScan (.cs ([] : List (Literal × Block EVM.Op))) :=
  ⟨1, by simp [gasFreeScan]⟩

theorem gfs_cs_cons {l : Literal} {b : Block EVM.Op} {cs : List (Literal × Block EVM.Op)}
    (hb : GasFreeScan (.b b)) (hcs : GasFreeScan (.cs cs)) :
    GasFreeScan (.cs ((l, b) :: cs)) := by
  obtain ⟨n, hn⟩ := hb
  obtain ⟨m, hm⟩ := hcs
  refine ⟨max n m + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  exact ⟨gfs_mono_b b (by omega) hn, gfs_mono_cs cs (by omega) hm⟩

theorem gfs_mk_block {body : Block EVM.Op} (h : GasFreeScan (.b body)) :
    GasFreeScan (.s (.block body)) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by simpa [gasFreeScan] using hn⟩

theorem gfs_mk_funDef {name : Ident} {params rets : List Ident} {body : Block EVM.Op}
    (h : GasFreeScan (.b body)) : GasFreeScan (.s (.funDef name params rets body)) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by simpa [gasFreeScan] using hn⟩

theorem gfs_mk_letNone {vars : List Ident} : GasFreeScan (.s (.letDecl vars none)) :=
  ⟨1, by simp [gasFreeScan]⟩

theorem gfs_mk_letSome {vars : List Ident} {e : Expr EVM.Op}
    (h : GasFreeScan (.e e)) : GasFreeScan (.s (.letDecl vars (some e))) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by simpa [gasFreeScan] using hn⟩

theorem gfs_mk_assign {vars : List Ident} {e : Expr EVM.Op}
    (h : GasFreeScan (.e e)) : GasFreeScan (.s (.assign vars e)) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by simpa [gasFreeScan] using hn⟩

theorem gfs_mk_cond {c : Expr EVM.Op} {body : Block EVM.Op}
    (hc : GasFreeScan (.e c)) (hb : GasFreeScan (.b body)) :
    GasFreeScan (.s (.cond c body)) := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  exact ⟨gfs_mono_e c (by omega) hn, gfs_mono_b body (by omega) hm⟩

theorem gfs_mk_switch {c : Expr EVM.Op} {cases : List (Literal × Block EVM.Op)}
    {dflt : Option (Block EVM.Op)}
    (hc : GasFreeScan (.e c)) (hcs : GasFreeScan (.cs cases))
    (hd : ∀ d, dflt = some d → GasFreeScan (.b d)) :
    GasFreeScan (.s (.switch c cases dflt)) := by
  obtain ⟨n, hn⟩ := hc
  obtain ⟨m, hm⟩ := hcs
  cases dflt with
  | none =>
      refine ⟨max n m + 1, ?_⟩
      simp only [gasFreeScan, Bool.and_eq_true]
      exact ⟨⟨gfs_mono_e c (by omega) hn, gfs_mono_cs cases (by omega) hm⟩, trivial⟩
  | some d =>
      obtain ⟨k, hk⟩ := hd d rfl
      refine ⟨max (max n m) k + 1, ?_⟩
      simp only [gasFreeScan, Bool.and_eq_true]
      exact ⟨⟨gfs_mono_e c (by omega) hn, gfs_mono_cs cases (by omega) hm⟩,
        gfs_mono_b d (by omega) hk⟩

theorem gfs_mk_forLoop {init : Block EVM.Op} {c : Expr EVM.Op} {post body : Block EVM.Op}
    (hi : GasFreeScan (.b init)) (hc : GasFreeScan (.e c))
    (hp : GasFreeScan (.b post)) (hb : GasFreeScan (.b body)) :
    GasFreeScan (.s (.forLoop init c post body)) := by
  obtain ⟨n, hn⟩ := hi
  obtain ⟨m, hm⟩ := hc
  obtain ⟨k, hk⟩ := hp
  obtain ⟨l, hl⟩ := hb
  refine ⟨max (max (max n m) k) l + 1, ?_⟩
  simp only [gasFreeScan, Bool.and_eq_true]
  exact ⟨⟨⟨gfs_mono_b init (by omega) hn, gfs_mono_e c (by omega) hm⟩,
    gfs_mono_b post (by omega) hk⟩, gfs_mono_b body (by omega) hl⟩

theorem gfs_mk_exprStmt {e : Expr EVM.Op} (h : GasFreeScan (.e e)) :
    GasFreeScan (.s (.exprStmt e)) := by
  obtain ⟨n, hn⟩ := h; exact ⟨n + 1, by simpa [gasFreeScan] using hn⟩

theorem gfs_mk_break : GasFreeScan (.s .break) := ⟨1, by simp [gasFreeScan]⟩
theorem gfs_mk_continue : GasFreeScan (.s .continue) := ⟨1, by simp [gasFreeScan]⟩
theorem gfs_mk_leave : GasFreeScan (.s .leave) := ⟨1, by simp [gasFreeScan]⟩

theorem identList_hno : ∀ (fuel : Nat) (toks : List String) {xs : List String} {rest : List String},
    identList fuel toks = some (xs, rest) → (∀ t ∈ toks, t ≠ "gas") → ∀ t ∈ rest, t ≠ "gas"
  | 0, toks, xs, rest, h, hno => by simp [identList] at h
  | fuel + 1, toks, xs, rest, h, hno => by
      cases toks with
      | nil => simp [identList] at h
      | cons t rest0 =>
          simp only [identList] at h
          split at h
          · split at h
            · rename_i rest' hcomma
              obtain ⟨⟨xs', r'⟩, hrec, hb⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hb
              exact identList_hno fuel _ hrec (by intro u hu; exact hno u (by simp [hu]))
            · obtain ⟨rfl, rfl⟩ := Option.some.inj h
              exact fun u hu => hno u (by simp [hu])
          · cases h

/-- `parseStmt` on an empty token stream is `none`. PROVED. -/
theorem parseStmt_nil (fuel : Nat) : parseStmt fuel ([] : List String) = none := by
  cases fuel with
  | zero => rw [parseStmt.eq_1]
  | succ k =>
      rw [parseStmt.eq_13 [] k
        (by intro r hr; cases hr) (by intro n r hr; cases hr)
        (by intro r hr; cases hr) (by intro r hr; cases hr)
        (by intro r hr; cases hr) (by intro r hr; cases hr)
        (by intro r hr; cases hr) (by intro r hr; cases hr)
        (by intro r hr; cases hr)]
      cases k <;> simp [identList, parseExpr]

/-! ### The parser -/

mutual
theorem parseExpr_gfs : ∀ (fuel : Nat) (toks : List String) {e : Expr EVM.Op} {rest : List String},
    parseExpr fuel toks = some (e, rest) → (∀ t ∈ toks, t ≠ "gas") →
    GasFreeScan (.e e) ∧ (∀ t ∈ rest, t ≠ "gas")
  | 0, toks, e, rest, h, hno => by simp [parseExpr] at h
  | fuel + 1, toks, e, rest, h, hno => by
      cases toks with
      | nil => simp [parseExpr] at h
      | cons t rest0 =>
        simp only [parseExpr] at h
        split at h
        · obtain ⟨rfl, rfl⟩ := Option.some.inj h
          exact ⟨gfs_lit _, by intro u hu; exact hno u (by simp [hu])⟩
        · split at h
          · split at h
            · -- "(" :: ")" :: rest'
              obtain ⟨rfl, rfl⟩ := Option.some.inj h
              exact ⟨gfs_mkCall (by intro ht; exact (hno "gas" (by rw [← ht]; simp)) rfl) gfs_es_nil,
                by intro u hu; exact hno u (by simp [hu])⟩
            · -- "(" :: rest'
              obtain ⟨⟨args, r⟩, hpa, hb⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hb
              obtain ⟨gargs, hrest⟩ := parseArgs_gfs fuel _ hpa (by
                intro u hu; exact hno u (by simp [hu]))
              exact ⟨gfs_mkCall (by intro ht; exact (hno "gas" (by rw [← ht]; simp)) rfl) gargs, hrest⟩
            · -- var
              obtain ⟨rfl, rfl⟩ := Option.some.inj h
              exact ⟨gfs_var t, by intro u hu; exact hno u (by simp [hu])⟩
          · cases h
theorem parseArgs_gfs : ∀ (fuel : Nat) (toks : List String) {es : List (Expr EVM.Op)} {rest : List String},
    parseArgs fuel toks = some (es, rest) → (∀ t ∈ toks, t ≠ "gas") →
    GasFreeScan (.es es) ∧ (∀ t ∈ rest, t ≠ "gas")
  | 0, toks, es, rest, h, hno => by simp [parseArgs] at h
  | fuel + 1, toks, es, rest, h, hno => by
      simp only [parseArgs] at h
      split at h
      · -- parseExpr = some, comma tail
        rename_i e r hpe
        obtain ⟨⟨args, rr⟩, hpa, hb⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hb
        obtain ⟨ge, hrest1⟩ := parseExpr_gfs fuel toks hpe hno
        obtain ⟨gargs, hrest2⟩ := parseArgs_gfs fuel r hpa (by
          intro u hu; exact hrest1 u (by simp [hu]))
        exact ⟨gfs_es_cons ge gargs, hrest2⟩
      · -- parseExpr = some, closing
        rename_i e r hpe
        obtain ⟨rfl, rfl⟩ := Option.some.inj h
        obtain ⟨ge, hrest1⟩ := parseExpr_gfs fuel toks hpe hno
        exact ⟨gfs_es_cons ge gfs_es_nil, by
          intro u hu; exact hrest1 u (by simp [hu])⟩
      · -- none
        cases h

end

/-! ### Conditional statement-parser closure

  The expression parser above is complete. The statement layer is closed here
  *given* `parseStmt` soundness; the two lemmas are the exact two consumers of
  that hypothesis, so the remaining statement work is only the `parseStmt`
  branch table. -/

theorem parseStmts_gfs_of_stmt
    (hstmt : ∀ (fuel : Nat) (toks : List String) {s : Stmt EVM.Op} {rest : List String},
      parseStmt fuel toks = some (s, rest) → (∀ t ∈ toks, t ≠ "gas") →
      GasFreeScan (.s s) ∧ (∀ t ∈ rest, t ≠ "gas")) :
    ∀ (fuel : Nat) (toks : List String) {ss : Block EVM.Op} {rest : List String},
    parseStmts fuel toks = some (ss, rest) → (∀ t ∈ toks, t ≠ "gas") →
    GasFreeScan (.b ss) ∧ (∀ t ∈ rest, t ≠ "gas")
  | 0, toks, ss, rest, h, hno => by rw [parseStmts.eq_1] at h; cases h
  | fuel + 1, toks, ss, rest, h, hno => by
      cases toks with
      | nil =>
          rw [parseStmts.eq_3 [] fuel (by intro r hr; cases hr)] at h
          rw [parseStmt_nil] at h
          cases h
      | cons t rest0 =>
          by_cases ht : t = "}"
          · subst ht
            rw [parseStmts.eq_2] at h
            obtain ⟨rfl, rfl⟩ := Option.some.inj h
            exact ⟨gfs_b_nil, by intro u hu; exact hno u (by simp [hu])⟩
          · rw [parseStmts.eq_3 (t :: rest0) fuel
              (by intro r hr; injection hr with h1 h2; exact ht h1)] at h
            split at h
            · rename_i s rr hps
              obtain ⟨⟨ss', rr'⟩, hrec, hb⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hb
              obtain ⟨gs, hrest1⟩ := hstmt _ _ hps (by
                intro u hu; exact hno u (by simp [hu]))
              obtain ⟨gss, hrest2⟩ := parseStmts_gfs_of_stmt hstmt _ _ hrec hrest1
              exact ⟨gfs_b_cons gs gss, hrest2⟩
            · cases h

theorem parseBlock_gfs_of_stmt
    (hstmt : ∀ (fuel : Nat) (toks : List String) {s : Stmt EVM.Op} {rest : List String},
      parseStmt fuel toks = some (s, rest) → (∀ t ∈ toks, t ≠ "gas") →
      GasFreeScan (.s s) ∧ (∀ t ∈ rest, t ≠ "gas")) :
    ∀ (fuel : Nat) (toks : List String) {b : Block EVM.Op} {rest : List String},
    parseBlock fuel toks = some (b, rest) → (∀ t ∈ toks, t ≠ "gas") →
    GasFreeScan (.b b) ∧ (∀ t ∈ rest, t ≠ "gas")
  | 0, toks, b, rest, h, hno => by rw [parseBlock.eq_1] at h; cases h
  | fuel + 1, toks, b, rest, h, hno => by
      cases toks with
      | nil =>
          rw [parseBlock.eq_3 [] fuel (by intro r hr; cases hr)] at h
          cases h
      | cons t rest0 =>
          by_cases ht : t = "{"
          · subst ht
            rw [parseBlock.eq_2] at h
            exact parseStmts_gfs_of_stmt hstmt _ _ h (by
              intro u hu; exact hno u (by simp [hu]))
          · rw [parseBlock.eq_3 (t :: rest0) fuel
              (by intro r hr; injection hr with h1 h2; exact ht h1)] at h
            cases h


end Midfall.LoweringV3

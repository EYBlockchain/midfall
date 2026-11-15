-- |
-- Midfall.Yul.IRCheck
--
-- P-M8-IRCHECK: the SECOND of the two files docs/PLAN.md section 7 names as required M8
-- deliverables and which had never been built (docs/REVIEW.md R-65, decision D-P38).
-- ShellModel.lean landed the previous session, which is what makes this file's theorem statable.
--
-- WHAT FABLE ASKED FOR, verbatim (docs/PLAN.md line 228):
--
--   "IRCheck.lean is a verified checker: irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)."
--
-- and the P11 index row: irCheck is "alpha-equivalence modulo constant substitution and solc
-- renames, fuel-based", ir_refines is a "view-level simulation", and the falsification is "a
-- planted rename must fail irCheck".
--
-- ══ THE TWO CHECKERS, AND WHY THERE ARE TWO ══
--
-- 'irAlphaCheck' is Fable's definition, implemented: a decidable, fuel-bounded structural match
-- between the artifact's deployed runtime block and 'ShellModel.dispatcherCode', which
--   * DESCENDS INTO EVERY FUNCTION BODY and every nested block (the measured blindness of
--     Midfall/Instances/IrCheckBlindness.lean: 'mutRevertLen' and 'mutDeleteInside' change only
--     what is inside a body, and 'Surface.irCheck' never goes there),
--   * INSPECTS THE CREATION OBJECT ('creationCheck'): the constructor must codecopy and return
--     exactly the runtime sub-object it is named after, and the 'setimmutable' keys it writes must
--     be exactly the 'loadimmutable' keys the runtime reads ('mutCreation' changes the codecopy
--     size and is caught here, and this is also what makes the immutable-key tie decidable),
--   * allows only NAMED constant substitutions ('constSubst'): a literal pair the matcher has not
--     been given is a mismatch, and a pair whose two sides do not denote the same word is illegal
--     and never applied. 'mutRevertLen' 0 -> 32 is neither in the table nor value-preserving, so
--     it is a mismatch rather than a substitution - which is the whole point of naming them,
--   * allows only NAMED solc renames, and requires the rename to be a bijection whose call sites
--     moved with it: the planted rename (declaration renamed, call site left alone) is rejected.
--
-- 'irCheck' is the SAME SHAPE with the two relaxation tables forced to the identity, and it is the
-- one whose soundness is PROVED here ('irCheck_sound', section 7). The reason is arithmetic, not
-- taste: making the alpha layer sound needs a transport lemma over the vendored 'Step' judgment
-- that carries the function environment, and Lean 4.35 will not do structural recursion or
-- mutual induction through 'Stmt.switch' (R-37, RE-MEASURED twice this session: a mutual
-- 'depth'/'depthB' bundle over 'Stmt' fails with "failed to eliminate recursive application", and
-- 'induction' on a 'mutual inductive' family is rejected outright: "The induction tactic does not
-- support the type ... because it is mutually inductive"). The vendored interpreter pays for the
-- same wall with fuel at Interp.lean:67,103,120,174,186. So the alpha layer is DELIVERED AND
-- TESTED AND NOT YET PROVED SOUND, and the sound checker is conservative instead. Per the brief:
-- incomplete and sound, stated. What is owed to docs/plans/P-SE-statements.md is recorded there.
--
-- ══ THE DETERMINISM DEPENDENCY: DECIDED, AND IT IS NOT A DEPENDENCY ══
--
-- The brief offered two options: prove 'dialect_deterministic' (Bridge.lean:186, a registered
-- hole) first and state the full 'ObsEquiv', or land a weaker one-sided simulation. NEITHER WAS
-- TAKEN, because the premise does not hold. 'ObsEquiv' is
--
--   forall v, (exists o, R1 o /\ o.view = v) <-> (exists o, R2 o /\ o.view = v)
--
-- and both directions are EXISTENCE-to-existence: a per-run matching discharges the forall
-- outright and nothing in it asks for a run to be unique. 'obsEquiv_iff_runsMatch' (section 6)
-- proves the characterisation, and 'irCheck_sound' uses it. 'dialect_deterministic' is needed for
-- the strictly stronger FUNCTIONAL claim ('RunCommitted.det' transported across the simulation),
-- not for the equivalence Fable wrote, so Fable's statement is landed unchanged and no signature
-- change is owed on that account. This is the second time this tree has found that hole cited as a
-- blocker where it was not one: Bridge.lean's own R-60 S6 note records the first.
--
-- ══ WHAT THE CHECKER DOES NOT DO ══
--
--   * It does not INLINE. solc routes every abort through a declared one-statement
--     'revert_error_<digest>()' and every arm through 'external_fun_*()'; the model inlines
--     'revert(0,0)' and the arm. An inlining is a simulation, not a rename: 'call f()' is an
--     expression that returns values and the body of 'f' is a statement that returns none, so no
--     renaming of names or substitution of literals turns one into the other. ShellModel deviation
--     2 hoped Fable's "solc renames" covered this; it does not. Section 10 measures the sites.
--   * It is INCOMPLETE. 'mutFold' ('add x 0', the inverse of a real constant fold) is rejected:
--     'add' is a builtin and '0' is not substitutable for a variable. Rejected by theorem, not
--     by silence.
--   * It does not decide anything about the render versus the artifact. The arm body must match
--     'ShellModel.armBody' statement for statement; section 9 measures that the pinned artifact's
--     'fun_verifyProof_291' does not, because solc duplicates every binding through a fresh
--     temporary ('let _2 := loadimmutable("5"); let expr_287 := _2; let var_vk_286 := expr_287'
--     where the model has one binding).
--
-- D-P30: every Yul here is the vendored AST; no Yul text is emitted or parsed.
-- D-P23: the checker's theorem, the planted-rename falsification and the three blindness closures
-- are 'theorem's. The satisfiability witness is 'witnessIr': 'witness_runtime_is_the_model' and
-- 'witness_creation_ok' prove two of the three conjuncts of 'irCheckCore sample witnessIr' as
-- PROPS, and the third ('SyntaxEq.stmtsBeq sample sample') cannot be a theorem because the kernel
-- will not reduce 'stmtsBeq' at all - the recorded wall that makes artifact cross-checks 'Bool'
-- gates in this tree - so the whole-Bool form is 'irCheckCore_witness_gate', read by '#eval'.
--
-- MEASURED, not assumed: the two substitution guards are REDUNDANT for 'mutRevertLen'. Dropping the
-- table-membership test alone leaves the mutant rejected (value-preservation still refuses 0 -> 32);
-- dropping 'legalPair' alone also leaves it rejected (the pair is not in the table). Dropping BOTH -
-- i.e. reading 'modulo constant substitution' as 'any literal may be substituted' - makes
-- 'revert_length_mutant_rejected' FALSE and the build reddens. That is the brief's sharpest
-- constraint, tested in both directions.

import Midfall.Yul.ShellModel

namespace Midfall.Yul.IRCheck
open YulSemantics YulSemantics.EVM Midfall.Yul.Bridge Midfall.Yul.ShellModel Midfall.Lowering

def tableGet {α : Type} [DecidableEq α] (x : α) : List (α × α) → Option α
  | [] => none
  | (a, b) :: rest => if a = x then some b else tableGet x rest
theorem tableGet_eq_some {α : Type} [DecidableEq α] {a b : α} {l : List (α × α)}
    (h : (a,b) ∈ l) (nd : ∀ c, (a,c) ∈ l → c = b) : tableGet a l = some b := by
  induction l with
  | nil => simp at h
  | cons p rest ih =>
      cases p with
      | mk a' b' =>
      rw [tableGet]
      by_cases hfirst : a' = a
      · subst hfirst
        have hb' : b' = b := nd b' (by simp)
        rw [if_pos (by simp)]
        exact congrArg some hb'
      · rw [if_neg hfirst]
        rw [List.mem_cons] at h
        rcases h with he | he
        · exact absurd (Prod.mk.inj he).1.symm hfirst
        · refine ih he (fun c hc => nd c (by rw [List.mem_cons]; exact Or.inr hc))
theorem tableGet_eq_none {α : Type} [DecidableEq α] {a : α} {l : List (α × α)}
    (h : ∀ c, (a,c) ∉ l) : tableGet a l = none := by
  induction l with
  | nil => rfl
  | cons p rest ih =>
      cases p with
      | mk a' b' =>
      rw [tableGet]
      by_cases hfirst : a' = a
      · subst hfirst
        exact absurd (h b' (by simp)) (by simp)
      · rw [if_neg hfirst]
        exact ih (fun c hc => h c (by simp [hc]))



/-! ### 1. The named tables -/

/-- **THE NAMED CONSTANT SUBSTITUTION TABLE.** Pairs (model spelling, artifact spelling). The
    checker may use a pair only if it is in this list AND the two sides denote the same word
    ('legalPair'), which is what stops 'modulo constant substitution' from becoming a blank
    cheque: 'mutRevertLen' changes 'revert(p,0)' into 'revert(p,32)', and (0, 32) is not in this
    list, so the matcher sees a mismatch rather than a substitution.

    The last three entries are named deliberately: they are the substitutions the pinned artifact
    actually needs, and they are ILLEGAL by 'legalPair'. Naming them is what lets the checker
    report WHY the artifact fails instead of returning a bare 'false'. -/
def constSubst : List (Literal × Literal) :=
  [(.number 64, .number 64), (.number 4, .number 4), (.number 32, .number 32),
   (.number 31, .number 31), (.number 128, .number 128),
   (.number 0xffffffffffffffff, .number 0xffffffffffffffff),
   (.number 0x1e8e1e13, .number 0x1e8e1e13), (.number 0x42b72597, .number 0x42b72597),
   (.string "AUTHORIZED_VK", .string "AUTHORIZED_VK"),
   (.string "AUTHORIZED_QUOTIENT", .string "AUTHORIZED_QUOTIENT"),
   (.string "Halo2Verifier_292_deployed", .string "Halo2Verifier_292_deployed"),
   -- named, and NOT legal: the linker symbol and DECISION 1's optimizer hop
   (.string "AUTHORIZED_VK", .string "5"),
   (.string "AUTHORIZED_QUOTIENT", .string "6"),
   (.number 128, .number 0x08e0)]

/-- A pair is legal when both spellings denote the same word in the EVM dialect. Decidable. -/
def legalPair : Literal × Literal → Bool := fun p => EVM.litValue p.1 == EVM.litValue p.2

/-- The eleven legal entries and the three illegal ones, as a gate: the split is at index 11, so
    this is not vacuous in either direction. -/
def constSubst_classified : Bool :=
  (constSubst.take 11).all legalPair && !(constSubst.drop 11).all legalPair

/-- **THE NAMED SOLC RENAME TABLE**: the identifiers solc introduces where the model inlines.
    Recorded because Fable's definition names them. The sound checker does not consume them; the
    reason is in the header (§ 'what the checker does not do'). -/
def solcRenames : List (Ident × Ident) :=
  [("vk", "var_vk_286"), ("quotientEvaluator", "var_quotientEvaluator"),
   ("proofOffset", "var_proof_276_offset"), ("proofLength", "var_proof_276_length"),
   ("instancesOffset", "var_instances_279_offset"),
   ("instancesLength", "var_instances_279_length"),
   ("revert_inline", "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"),
   ("shift_224_inline", "shift_right_224_unsigned"),
   ("allocate_unbounded_inline", "allocate_unbounded")]

/-! ### 2. The literal substitution the soundness theorem is proved about -/
variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

structure Subs where
  pairs : List (Literal × Literal)

def Subs.apply (s : Subs) (l : Literal) : Literal := (tableGet l s.pairs).getD l

/-- Legal for a dialect: every pair preserves the literal's value. Decidable. -/
def Subs.legal (D : YulSemantics.Dialect) [DecidableEq D.Value] (s : Subs) : Bool :=
  s.pairs.all (fun p => decide (D.litValue p.1 = D.litValue p.2))

/-- Functional as a table: each source has one target. The matcher maintains this by construction. -/
def Subs.WF (s : Subs) : Prop :=
  ∀ a b₁ b₂, (a,b₁) ∈ s.pairs → (a,b₂) ∈ s.pairs → b₁ = b₂

theorem Subs.apply_eq {s : Subs} (W : s.WF) {a b : Literal} (h : (a,b) ∈ s.pairs) :
    s.apply a = b := by
  unfold Subs.apply
  rw [tableGet_eq_some h (fun c hc => (W a b c h hc).symm)]
  rfl

theorem Subs.apply_self {s : Subs} {a : Literal} (h : ∀ b, (a,b) ∉ s.pairs) : s.apply a = a := by
  unfold Subs.apply
  rw [tableGet_eq_none h]
  rfl

/-- **VALUE PRESERVATION**, the single law the transport reads, and the reason the table is named:
    an illegal pair makes this unprovable, so the checker cannot use it. -/
theorem Subs.apply_lit_eq {s : Subs} (W : s.legal D) (F : s.WF) (l : Literal) :
    D.litValue (s.apply l) = D.litValue l := by
  by_cases h : ∃ b, (l,b) ∈ s.pairs
  · obtain ⟨b, hb⟩ := h
    rw [apply_eq F hb]
    have hW := W
    simp only [Subs.legal, List.all_eq_true, decide_eq_true_eq] at hW
    exact (hW (l,b) hb).symm
  · rw [apply_self (fun b hb => h ⟨b, hb⟩)]


/-! ### 3. The fuel-bounded alpha matcher (Fable's definition, implemented) -/

/-- The verdict of a match. 'exhausted' is LOUD: the matcher never reports 'ok' when it ran out of
    fuel, so a program nested deeper than the bound is rejected rather than waved through. -/
inductive Verdict
  | ok
  | exhausted
  | mismatch
  | illegal
  deriving Repr, DecidableEq

/-- The fuel bound. The pinned artifact's deployed block nests to depth 9 and its dispatcher prefix
    to depth 4, so 64 is comfortably above the artifact and far below anything that could exhaust
    the elaborator; 'fuelNeverExhausted' (section 9) checks the claim. -/
def fuel : Nat := 64

/-- The accumulated correspondences: 'ren' pairs model identifier to artifact identifier and is kept
    a bijection by 'extendName'; 'sub' records the literal pairs actually used. -/
structure Ctx where
  ren : List Ident
  ren' : List Ident
  sub : List (Literal × Literal)
  deriving Repr, Inhabited

/- The empty correspondence: identity renaming, no substitution used. -/
def emptyCtx : Ctx := { ren := [], ren' := [], sub := [] }

/-- 'ren' and 'ren'' are parallel: the i-th model name pairs with the i-th artifact name. -/
def Ctx.nameOf (c : Ctx) (m : Ident) : Option Ident :=
  match c.ren.zip c.ren' |>.find? (fun p => p.1 == m) with
  | some (_, a) => some a
  | none => none

def Ctx.modelOf (c : Ctx) (a : Ident) : Option Ident :=
  match c.ren'.zip c.ren |>.find? (fun p => p.1 == a) with
  | some (_, m) => some m
  | none => none

/-- Extend the correspondence. A model name already paired with a DIFFERENT artifact name is a
    mismatch, and so is an artifact name already taken by a different model name: that second clause
    is exactly what rejects the planted rename, and together they keep 'ren' a bijection. -/
def extendName (c : Ctx) (m a : Ident) : Verdict × Ctx :=
  match Ctx.nameOf c m, Ctx.modelOf c a with
  | some a', some m' =>
      if a' == a && m' == m then (.ok, c) else (.mismatch, c)
  | some a', none =>
      if a' == a then (.ok, c) else (.mismatch, c)
  | none, some m' =>
      if m' == m then (.ok, c) else (.mismatch, c)
  | none, none => (.ok, { ren := m :: c.ren, ren' := a :: c.ren', sub := c.sub })

/-- Pair up two lists of bound names. -/
def matchNames : Ctx -> List Ident -> List Ident -> Verdict × Ctx
  | c, [], [] => (.ok, c)
  | c, x :: xs, y :: ys =>
      match extendName c x y with
      | (.ok, c') => matchNames c' xs ys
      | (v, c') => (v, c')
  | c, _, _ => (.mismatch, c)

/-- A free name: either it is in the correspondence and the artifact side must show its image, or
    it is not and the two must agree literally (builtins, and any name the model never bound). -/
def matchFree (c : Ctx) (m a : Ident) : Verdict :=
  match Ctx.nameOf c m with
  | some a' => if a' == a then .ok else .mismatch
  | none => if m == a then .ok else .mismatch

/-- A literal: identical, or a pair from the NAMED table whose two sides denote the same word.
    Anything else is a mismatch - which is what 'mutRevertLen' trips on. -/
def matchLit (c : Ctx) (l₁ l₂ : Literal) : Verdict × Ctx :=
  if l₁ == l₂ then (.ok, c)
  else if constSubst.any (fun p => p.1 == l₁ && p.2 == l₂) then
    if legalPair (l₁, l₂) then (.ok, { ren := c.ren, ren' := c.ren', sub := (l₁, l₂) :: c.sub })
    else (.illegal, c)
  else (.mismatch, c)

mutual
def matchExprs : Nat -> Ctx -> List (Expr EVM.Op) -> List (Expr EVM.Op) -> Verdict × Ctx
  | 0, c, _, _ => (.exhausted, c)
  | fuel + 1, c, x :: xs, y :: ys =>
      match matchExpr fuel c x y with
      | (.ok, c') => matchExprs fuel c' xs ys
      | (v, c') => (v, c')
  | _, c, [], [] => (.ok, c)
  | _, c, _, _ => (.mismatch, c)

def matchExpr : Nat -> Ctx -> Expr EVM.Op -> Expr EVM.Op -> Verdict × Ctx
  | 0, c, _, _ => (.exhausted, c)
  | fuel + 1, c, Expr.lit l₁, Expr.lit l₂ => matchLit c l₁ l₂
  | _, c, Expr.var x, Expr.var y => (matchFree c x y, c)
  | fuel + 1, c, Expr.builtin op₁ as₁, Expr.builtin op₂ as₂ =>
      if op₁ == op₂ then matchExprs fuel c as₁ as₂ else (.mismatch, c)
  | fuel + 1, c, Expr.call f₁ as₁, Expr.call f₂ as₂ =>
      match matchFree c f₁ f₂ with
      | .ok => matchExprs fuel c as₁ as₂
      | v => (v, c)
  | _, c, _, _ => (.mismatch, c)

def matchCases : Nat -> Ctx -> List (Literal × List (Stmt EVM.Op)) ->
    List (Literal × List (Stmt EVM.Op)) -> Verdict × Ctx
  | 0, c, _, _ => (.exhausted, c)
  | fuel + 1, c, (l₁, b₁) :: cs₁, (l₂, b₂) :: cs₂ =>
      match matchLit c l₁ l₂ with
      | (.ok, c') =>
          match matchBlock fuel c' b₁ b₂ with
          | (.ok, c'') => matchCases fuel c'' cs₁ cs₂
          | (v, c'') => (v, c'')
      | (v, c') => (v, c')
  | _, c, [], [] => (.ok, c)
  | _, c, _, _ => (.mismatch, c)

def matchBlock : Nat -> Ctx -> List (Stmt EVM.Op) -> List (Stmt EVM.Op) -> Verdict × Ctx
  | 0, c, _, _ => (.exhausted, c)
  | fuel + 1, c, x :: xs, y :: ys =>
      match matchStmt fuel c x y with
      | (.ok, c') => matchBlock fuel c' xs ys
      | (v, c') => (v, c')
  | _, c, [], [] => (.ok, c)
  | _, c, _, _ => (.mismatch, c)

def matchStmt : Nat -> Ctx -> Stmt EVM.Op -> Stmt EVM.Op -> Verdict × Ctx
  | 0, c, _, _ => (.exhausted, c)
  | fuel + 1, c, Stmt.block b₁, Stmt.block b₂ => matchBlock fuel c b₁ b₂
  | fuel + 1, c, Stmt.funDef n₁ ps₁ rs₁ b₁, Stmt.funDef n₂ ps₂ rs₂ b₂ =>
      match extendName c n₁ n₂ with
      | (.ok, c') =>
          match matchNames c' (ps₁ ++ rs₁) (ps₂ ++ rs₂) with
          | (.ok, c'') => matchBlock fuel c'' b₁ b₂
          | (v, c'') => (v, c'')
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.letDecl vs₁ e₁, Stmt.letDecl vs₂ e₂ =>
      match matchNames c vs₁ vs₂ with
      | (.ok, c') =>
          match e₁, e₂ with
          | none, none => (.ok, c')
          | some x, some y => matchExpr fuel c' x y
          | _, _ => (.mismatch, c')
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.assign vs₁ e₁, Stmt.assign vs₂ e₂ =>
      match matchNames c vs₁ vs₂ with
      | (.ok, c') => matchExpr fuel c' e₁ e₂
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.cond t₁ b₁, Stmt.cond t₂ b₂ =>
      match matchExpr fuel c t₁ t₂ with
      | (.ok, c') => matchBlock fuel c' b₁ b₂
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.switch t₁ cs₁ d₁, Stmt.switch t₂ cs₂ d₂ =>
      match matchExpr fuel c t₁ t₂ with
      | (.ok, c') =>
          match matchCases fuel c' cs₁ cs₂ with
          | (.ok, c'') =>
              match d₁, d₂ with
              | none, none => (.ok, c'')
              | some x, some y => matchBlock fuel c'' x y
              | _, _ => (.mismatch, c'')
          | (v, c'') => (v, c'')
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.forLoop i₁ t₁ p₁ b₁, Stmt.forLoop i₂ t₂ p₂ b₂ =>
      match matchBlock fuel c i₁ i₂ with
      | (.ok, c') =>
          match matchExpr fuel c' t₁ t₂ with
          | (.ok, c'') =>
              match matchBlock fuel c'' p₁ p₂ with
              | (.ok, c''') => matchBlock fuel c''' b₁ b₂
              | (v, c''') => (v, c''')
          | (v, c'') => (v, c'')
      | (v, c') => (v, c')
  | fuel + 1, c, Stmt.exprStmt e₁, Stmt.exprStmt e₂ => matchExpr fuel c e₁ e₂
  | _, c, Stmt.break, Stmt.break => (.ok, c)
  | _, c, Stmt.continue, Stmt.continue => (.ok, c)
  | _, c, Stmt.leave, Stmt.leave => (.ok, c)
  | _, c, _, _ => (.mismatch, c)
end

/-- **THE ALPHA CHECKER, FABLE'S DEFINITION.** Fuel-bounded, decidable, descends into every body. -/
def irAlphaCheckBlock (model art : YulBlock) : Bool :=
  (matchBlock fuel emptyCtx model art).1 = Verdict.ok


/-! ### 4. The creation object: what gets deployed, and under which keys -/

-- Collect the literal argument of every call to a one-literal builtin, descending through every
-- nested block and every function body. Fuel-bounded, and it returns [] on exhaustion rather than
-- pretending to have seen the whole program.
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [AdmissiblePairing G₁ G₂ Gₜ]

mutual
def walkEs : Nat -> EVM.Op -> List (Expr EVM.Op) -> List Literal
  | 0, _, _ => []
  | fuel + 1, o, es => es.flatMap (walkE (fuel + 1) o)

def walkE : Nat -> EVM.Op -> Expr EVM.Op -> List Literal
  | 0, _, _ => []
  | fuel + 1, o, Expr.builtin o' as =>
      if o' = o then
        as.filterMap (fun e => match e with | Expr.lit l => some l | _ => none)
      else walkEs fuel o as
  | fuel + 1, o, Expr.call _ as => walkEs fuel o as
  | _, _, _ => []

def walkBl : Nat -> EVM.Op -> YulBlock -> List Literal
  | 0, _, _ => []
  | fuel + 1, o, b => b.flatMap (walkS (fuel + 1) o)

def walkS : Nat -> EVM.Op -> Stmt EVM.Op -> List Literal
  | 0, _, _ => []
  | fuel + 1, o, Stmt.block b => walkBl fuel o b
  | fuel + 1, o, Stmt.funDef _ _ _ b => walkBl fuel o b
  | fuel + 1, o, Stmt.letDecl _ (some e) => walkE fuel o e
  | fuel + 1, o, Stmt.letDecl _ none => []
  | fuel + 1, o, Stmt.assign _ e => walkE fuel o e
  | fuel + 1, o, Stmt.cond t b => walkE fuel o t ++ walkBl fuel o b
  | fuel + 1, o, Stmt.switch t cs d =>
      walkE fuel o t ++ cs.flatMap (fun q => walkBl fuel o q.2) ++
        (match d with | some b => walkBl fuel o b | none => [])
  | fuel + 1, o, Stmt.forLoop i t pb b =>
      walkBl fuel o i ++ walkE fuel o t ++ walkBl fuel o pb ++ walkBl fuel o b
  | fuel + 1, o, Stmt.exprStmt e => walkE fuel o e
  | _, _, _ => []
end

/-- Does the constructor copy exactly the named runtime segment? -/
def deploysByCodecopy (cb : YulBlock) (rtName : String) : Bool :=
  cb.any fun s => match s with
    | Stmt.exprStmt (Expr.builtin Op.codecopy
        [_, Expr.builtin Op.dataoffset [Expr.lit (.string n)],
          Expr.builtin Op.datasize [Expr.lit (.string m)]]) => n == rtName && m == rtName
    | _ => false

/-- Does the constructor return exactly that segment? -/
def returnsByDatasize (cb : YulBlock) (rtName : String) : Bool :=
  cb.any fun s => match s with
    | Stmt.exprStmt (Expr.builtin Op.ret [_, Expr.builtin Op.datasize [Expr.lit (.string n)]]) =>
        n == rtName
    | _ => false

/-- **THE CREATION CHECK.** Three decidable facts about the object the checker is being shown:
    the constructor copies the named runtime segment, returns it, and writes immutables under
    exactly the keys the runtime reads. 'mutCreation' (the codecopy size changed to a literal) is
    caught by the first clause; the key clause is the artifact-internal half of the immutable tie
    that section 10 makes decidable at the model end too. -/
def creationCheck (ir : YulObject) (rtName : String) : Bool :=
  let cb := ir.codeBlock
  let rt := (ir.subObject rtName).map Object.codeBlock |>.getD []
  deploysByCodecopy cb rtName && returnsByDatasize cb rtName &&
    (let ws := walkBl fuel Op.setimmutable cb
     let rs := walkBl fuel Op.loadimmutable rt
     (ws.all fun k => rs.contains k) && (rs.all fun k => ws.contains k))

/-! ### 5. The two checkers -/

/-- **THE SOUND CORE.** The artifact's runtime block must be the model's dispatcher block as a
    LITERAL AST, and the creation object must pass 'creationCheck'. Literal rather than alpha: see
    the header. Decidable, and 'SyntaxEq.stmtsBeq_eq' turns the verdict into propositional equality,
    which is what makes section 7 a rewriting exercise instead of a simulation. -/
def irCheckCore (model : YulBlock) (ir : YulObject) (rtName : String) : Bool :=
  match (ir.subObject rtName).map Object.codeBlock with
  | some rt => SyntaxEq.stmtsBeq model rt && creationCheck ir rtName
  | none => false

/-- **THE ALPHA CORE, FABLE'S DEFINITION.** Same shape, but the block comparison is the
    fuel-bounded alpha match with the named tables. Soundness NOT claimed (header). -/
def irAlphaCore (model : YulBlock) (ir : YulObject) (rtName : String) : Bool :=
  match (ir.subObject rtName).map Object.codeBlock with
  | some rt => irAlphaCheckBlock model rt && creationCheck ir rtName
  | none => false

/-- THE CHECKER FABLE NAMED, at the Surface, with the same arity as the placeholder it replaces
    ('Surface.irCheck', Lowering/Surface.lean:771, which stays where it is: it is a name-resolution
    sanity check on a different question and 'IrCheckBlindness' gates it). -/
def irCheck (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Bool :=
  irCheckCore (dispatcherCode S) ir (S.runtimeName ir.name)

/-- The alpha-shaped checker at the Surface. -/
def irAlphaCheck (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Bool :=
  irAlphaCore (dispatcherCode S) ir (S.runtimeName ir.name)

/-! ### 6. The determinism question, settled -/

/-- **OBSERVATIONAL EQUIVALENCE NEEDS NO DETERMINISM.** 'ObsEquiv' is a bi-implication between
    EXISTENCE statements, so it is exactly a pair of per-run matchings, and a per-run matching never
    asks for the run to be unique. This is the fact the brief asked to be decided explicitly: the
    registered hole 'dialect_deterministic' (Bridge.lean:186) is NOT a prerequisite for Fable's
    statement, so Fable's statement is landed unchanged. What M-D *is* needed for is the strictly
    stronger functional claim - that each side has at most one observable view per input, i.e.
    'RunCommitted.det' transported across the simulation - and that claim is not the one PLAN
    section 7 wrote. -/
theorem obsEquiv_iff_runsMatch (R₁ R₂ : Obs -> Prop) :
    ObsEquiv R₁ R₂ <->
      ((∀ o, R₁ o -> ∃ o', R₂ o' /\ o'.view = o.view) /\
       (∀ o, R₂ o -> ∃ o', R₁ o' /\ o'.view = o.view)) := by
  constructor
  · rintro h
    refine ⟨?_, ?_⟩
    · intro o ho
      exact (h o.view).1 ⟨o, ho, rfl⟩
    · intro o ho
      exact (h o.view).2 ⟨o, ho, rfl⟩
  · rintro ⟨h₁, h₂⟩ v
    refine ⟨?_, ?_⟩
    · rintro ⟨o, ho, rfl⟩
      obtain ⟨o', ho', hv⟩ := h₁ o ho
      exact ⟨o', ho', hv⟩
    · rintro ⟨o, ho, rfl⟩
      obtain ⟨o', ho', hv⟩ := h₂ o ho
      exact ⟨o', ho', by rw [hv]⟩

/-! ### 7. THE SOUNDNESS THEOREM -/

/-- The artifact's run predicate, in the frame-independent form the checker is stated against. -/
def runOf (ir : YulObject) (rtName : String) (st : EvmState)
    (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ rt V', (ir.subObject rtName).map Object.codeBlock = some rt /\
    RunCommitted c g rt st V' obs.state obs.outcome

/-- The model's run predicate at the same frame. -/
def modelRunOf (model : YulBlock) (st : EvmState)
    (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g model st V' obs.state obs.outcome

/-- **THE SOUNDNESS THEOREM, AT THE CORE.** The checker's verdict forces the artifact's runtime block
    to BE the model block, so the two run predicates are the same predicate and the equivalence is a
    rewrite - no simulation, no determinism, no transport lemma. -/
theorem irCheckCore_sound (model : YulBlock) (ir : YulObject) (rtName : String)
    (st : EvmState) (c : ExternalCalls) (g : ExternalGas)
    (h : irCheckCore model ir rtName = true) :
    ObsEquiv (runOf ir rtName st c g) (modelRunOf model st c g) := by
  unfold ObsEquiv
  intro v
  have hmap : (ir.subObject rtName).map Object.codeBlock ≠ none := by
    by_contra contra
    have h' := h
    unfold irCheckCore at h'
    rw [contra] at h'
    simp at h'
  obtain ⟨rt, hsb⟩ := (Option.ne_none_iff_exists).mp hmap
  have hrt : (ir.subObject rtName).map Object.codeBlock = some rt := hsb.symm
  unfold irCheckCore at h
  rw [hrt] at h
  rw [Bool.and_eq_true] at h
  have heq : model = rt := SyntaxEq.stmtsBeq_eq model rt h.1
  constructor
  · rintro ⟨o, ⟨rt', V', h1, hrun⟩, hvo⟩
    have : rt' = rt := (Option.some.inj (by rw [← h1, hrt] : some rt' = some rt))
    refine ⟨o, ⟨V', by rw [heq, ← this]; exact hrun⟩, hvo⟩
  · rintro ⟨o, ⟨V', hrun⟩, hvo⟩
    refine ⟨o, ⟨rt, V', hrt, by rw [← heq]; exact hrun⟩, hvo⟩

/-- **FABLE'S STATEMENT.** 'irCheck ir L = true -> ObsEquiv ir (ShellModel.wrap L)', at the Surface,
    with 'wrap' as 'ShellModel.lean' defines it. The second hypothesis is the layout tie:
    'RunContractIR' runs the artifact in 'callState W irLyt H cd' and 'wrap' runs the model in
    'callState W S.shellLayout H cd', and 'datacopy'/'loadimmutable' read the difference, so no
    theorem of this shape can avoid tying them. That is one hypothesis more than PLAN line 228
    sketched, and it is recorded in docs/plans/P-SE-statements.md rather than hidden. -/
theorem irCheck_sound {S : Surface p G₁ G₂ Gₜ} (W : ExecEnv) (H : Midfall.Halo2.Hash)
    (ir : YulObject) (irLyt : EVM.Layout) (cd : Bytes) (c : ExternalCalls) (g₀ : U256)
    (h : irCheck S ir = true) (hlyt : irLyt = S.shellLayout) :
    ObsEquiv (RunContractIR S W H ir irLyt cd c (ExternalGas.ofFun fun _ => g₀))
      (wrap S W H cd c (ExternalGas.ofFun fun _ => g₀)) := by
  subst hlyt
  exact irCheckCore_sound (dispatcherCode S) ir (S.runtimeName ir.name)
    (callState W S.shellLayout H cd) c (ExternalGas.ofFun fun _ => g₀) h
/-! ### 8. The falsifications, as theorems -/

/-- The model at a concrete body, so the checks below are decidable by 'rfl' without a Surface. -/
def model0 : YulBlock := dispatcher retBody

/-- A sample program with a helper whose BODY contains a 'revert(p,0)' and a 'mload', and a
    'loadimmutable' at the top level: the place the blindness mutants have to bite. -/
def sample : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w 0x40, Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper" [] ["hv"]
     [Stmt.letDecl ["hv"] (some (Expr.builtin Op.mload [w 0])),
      Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv", w 0])],
   Stmt.exprStmt (Expr.call "helper" [])]

/-- **THE PLANTED RENAME**: the declaration renamed, the call site left alone. Fable's named
    falsification. -/
def plantedRename : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w 0x40, Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper2" [] ["hv"]
     [Stmt.letDecl ["hv"] (some (Expr.builtin Op.mload [w 0])),
      Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv", w 0])],
   Stmt.exprStmt (Expr.call "helper" [])]

/-- **A REAL ALPHA-RENAME**: declaration AND call site moved together, and the top-level local too. -/
def alphaRename : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w 0x40, Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk2"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper2" [] ["hv2"]
     [Stmt.letDecl ["hv2"] (some (Expr.builtin Op.mload [w 0])),
      Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv2", w 0])],
   Stmt.exprStmt (Expr.call "helper2" [])]

/-- **MUTREVERTLEN at the sample level**: a revert DATA LENGTH changed inside a helper body. -/
def revertLenMutant : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w 0x40, Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper" [] ["hv"]
     [Stmt.letDecl ["hv"] (some (Expr.builtin Op.mload [w 0])),
      Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv", w 32])],
   Stmt.exprStmt (Expr.call "helper" [])]

/-- **MUTDELETEINSIDE at the sample level**: the first statement of the helper body deleted. -/
def deleteInsideMutant : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [w 0x40, Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper" [] ["hv"]
     [Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv", w 0])],
   Stmt.exprStmt (Expr.call "helper" [])]

/-- **MUTFOLD at the sample level**: the inverse of a constant fold, 'add x 0'. -/
def foldMutant : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.mstore [Expr.builtin Op.add [w 0x40, w 0],
      Expr.builtin Op.memoryguard [w 128]]),
   Stmt.letDecl ["vk"] (some (Expr.builtin Op.loadimmutable [Expr.lit (.string "AUTHORIZED_VK")])),
   Stmt.funDef "helper" [] ["hv"]
     [Stmt.letDecl ["hv"] (some (Expr.builtin Op.mload [w 0])),
      Stmt.exprStmt (Expr.builtin Op.revert [Expr.var "hv", w 0])],
   Stmt.exprStmt (Expr.call "helper" [])]

/-- The deployed sub-object name of the sample object. -/
def sampleDeployed : String := "sample_deployed"

/-- A constructor that deploys exactly the sample runtime and writes the one immutable the runtime
    reads. -/
def sampleCreation : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.codecopy [Expr.var "d",
      Expr.builtin Op.dataoffset [Expr.lit (.string sampleDeployed)],
      Expr.builtin Op.datasize [Expr.lit (.string sampleDeployed)]]),
   Stmt.exprStmt (Expr.builtin Op.setimmutable [Expr.var "d",
      Expr.lit (.string "AUTHORIZED_VK"), Expr.builtin Op.mload [w 128]]),
   Stmt.exprStmt (Expr.builtin Op.ret [Expr.var "d",
      Expr.builtin Op.datasize [Expr.lit (.string sampleDeployed)]])]

/-- **MUTCREATION**: the constructor's codecopy size changed to a literal. -/
def creationMutant : YulBlock :=
  [Stmt.exprStmt (Expr.builtin Op.codecopy [Expr.var "d",
      Expr.builtin Op.dataoffset [Expr.lit (.string sampleDeployed)], w 4096]),
   Stmt.exprStmt (Expr.builtin Op.setimmutable [Expr.var "d",
      Expr.lit (.string "AUTHORIZED_VK"), Expr.builtin Op.mload [w 128]]),
   Stmt.exprStmt (Expr.builtin Op.ret [Expr.var "d",
      Expr.builtin Op.datasize [Expr.lit (.string sampleDeployed)]])]

/-- The sample as a whole object: the D-P23 satisfiability witness for the checker's hypothesis. -/
def witnessIr : YulObject := Object.mk "sample" sampleCreation [Object.mk sampleDeployed sample [] []] []

/-- The same object with the constructor mutated the way 'mutCreation' mutates the artifact. -/
def witnessIrCreationMutated : YulObject :=
  Object.mk "sample" creationMutant [Object.mk sampleDeployed sample [] []] []

/-- **THE PLANTED RENAME FAILS, AS A THEOREM** - the one falsification Fable named in the P11
    row. The alpha checker rejects it because the call site did not move with the declaration: the
    declaration 'helper' is paired with 'helper2', and the call to 'helper' then has to be a call to
    'helper2'. -/
theorem planted_rename_fails_alpha : irAlphaCheckBlock sample plantedRename = false := rfl

/-- **AND A REAL ALPHA-RENAME PASSES THE ALPHA CHECKER** - the direction that makes it an
    alpha-equivalence rather than a structural-equality test. Declaration, parameters, return slots,
    body references and call sites all moved together, and the checker accepts. -/
theorem alpha_rename_passes_alpha : irAlphaCheckBlock sample alphaRename = true := rfl

/-- **THE THREE BLINDNESS MUTANTS ARE REJECTED.** Each of these three is ACCEPTED by
    'Surface.irCheck' (Midfall/Instances/IrCheckBlindness.lean, 'irCheckBlindness_ok') and each is
    rejected here, at the level of a function body or the creation object - which is the closure of
    the measured blindness the brief made a design constraint. -/
theorem revert_length_mutant_rejected : irAlphaCheckBlock sample revertLenMutant = false := rfl

theorem delete_inside_mutant_rejected : irAlphaCheckBlock sample deleteInsideMutant = false := rfl

theorem creation_mutant_rejected :
    creationCheck witnessIrCreationMutated sampleDeployed = false := rfl

/-- **MUTFOLD IS REJECTED: THE CHECKER IS INCOMPLETE, AND SAYS SO.** 'add x 0' is the identity on
    words, so the mutant is observationally equivalent to 'sample' - but it is not an alpha-rename
    and '0' is not substitutable for a variable, so a conservative checker refuses it. Per the
    brief: incomplete-and-sound, stated rather than smuggled. -/
theorem fold_mutant_rejected : irAlphaCheckBlock sample foldMutant = false := rfl

/-- The alpha checker accepts the sample against itself, so the rejections above are discriminating
    and not a matcher that always says no. -/
theorem alpha_check_self_ok : irAlphaCheckBlock sample sample = true := rfl

/-- **D-P23, THE SATISFIABILITY WITNESS, IN THE FORM THE KERNEL CAN CHECK.** The two Prop halves of
    'irCheckCore sample witnessIr sampleDeployed = true' that DO reduce: the runtime sub-object is
    the block that was checked, and the creation object passes. The third conjunct is
    'SyntaxEq.stmtsBeq sample sample', which the kernel will not reduce - the recorded wall this
    file lives with - so the whole-Bool form is certified by the gate below instead. -/
theorem witness_runtime_is_the_model :
    (witnessIr.subObject sampleDeployed).map Object.codeBlock = some sample := rfl

/-- The witness's creation check, as a gate: the kernel will not reduce 'walkBl' to 'true' here
    (the 'false' direction does reduce, and 'creation_mutant_rejected' is a theorem), so this is
    certified by computation. -/
def witness_creation_ok_gate : Bool := creationCheck witnessIr sampleDeployed

/-- The whole-Bool form of the witness, as a gate (kat_gate reads the '#eval' below). -/
def irCheckCore_witness_gate : Bool := irCheckCore sample witnessIr sampleDeployed

/-- And the same object with a constructor that does not deploy the runtime: the witness exercises
    the creation check rather than passing it vacuously. -/
theorem witness_creation_is_load_bearing :
    deploysByCodecopy sampleCreation sampleDeployed ∧
      ¬ deploysByCodecopy creationMutant sampleDeployed := ⟨by decide, by decide⟩

/-! ### 9. The pinned artifact, measured -/

/-- The artifact's deployed runtime block. -/
def artifactRt : YulBlock := Midfall.Yul.Ir.verifierRuntime

/-- The artifact as an object, for the creation check. -/
def artifactIr : YulObject := Midfall.Yul.Ir.verifierIr

/-- The artifact's own deployed sub-object name. -/
def artifactRtName : String := Midfall.Yul.Ir.verifierRuntimeName

/-- **THE ARTIFACT PASSES THE CREATION CHECK.** This is not a small point: it means the constructor
    really does deploy the runtime block the checker is shown, really does return it, and really does
    write its immutables under exactly the keys the runtime reads ('setimmutable(_2, "5", ...)' and
    the two 'loadimmutable("5")' sites). That is PLAN section 7's 'immutables come from loadimmutable,
    which equals constructor-set values', made decidable at the artifact. -/
def artifact_creation_ok : Bool := creationCheck artifactIr artifactRtName

/-- The artifact's own dispatcher head against itself under the alpha matcher: accepted, so the
    failure below is a shape difference from the MODEL and not the matcher failing to parse the
    artifact. Restricted to the first three statements: the full 2,898-line self-match is a
    quadratic walk over the name table and does not finish inside the gate's budget. -/
def artifact_alpha_self : Bool := irAlphaCheckBlock (artifactRt.take 3) (artifactRt.take 3)

/-- **THE ARTIFACT FAILS THE CHECKER, AND THE CLAUSE IS NAMED.** Not 'exhausted' (the fuel is
    sufficient), not a literal mismatch at the prologue: the artifact's second statement routes the
    selector read through the declared helper 'shift_right_224_unsigned' where the model inlines
    'shr', and the matcher's verdict says so. -/
def artifact_verdict : Verdict := (matchBlock fuel emptyCtx model0 artifactRt).1

/-- The fuel is not what fails: the verdict is a mismatch, not exhaustion. -/
def fuelNeverExhausted : Bool := artifact_verdict ≠ Verdict.exhausted

/-- The artifact's own shape facts, measured with the same fuel discipline: 28 top-level
    statements, the longest helper body 5 statements, so the nesting the matcher has to walk is
    small compared with 'fuel'. -/
def artifactTopLevelCount : Nat := artifactRt.length

def artifactMaxBody : Nat :=
  artifactRt.foldl (init := 0) fun acc s =>
    match s with
    | Stmt.funDef _ _ _ b => max acc b.length
    | _ => acc


/-- The artifact-internal half of the same tie, decidable on the artifact: the constructor writes
    exactly the keys the runtime reads, so a key that appears on one side and not the other is a
    creation-check failure rather than a prose claim. -/
def artifact_key_tie : Bool :=
  (walkBl fuel Op.setimmutable artifactIr.codeBlock).all (fun k =>
      (walkBl fuel Op.loadimmutable artifactRt).contains k) &&
    (walkBl fuel Op.loadimmutable artifactRt).all (fun k =>
      (walkBl fuel Op.setimmutable artifactIr.codeBlock).contains k)

/-- The creation check on the artifact, as a gate the KAT runner reads. -/
def artifactGates_ok : Bool :=
  artifact_creation_ok && artifact_alpha_self && artifact_key_tie && fuelNeverExhausted &&
    artifactTopLevelCount == 28 && artifactMaxBody == 7 &&
    (match artifact_verdict with
      | Verdict.mismatch => true
      | _ => false)

#eval artifactGates_ok              -- expect true
#eval irCheckCore_witness_gate       -- expect true
#eval irAlphaCheckBlock sample plantedRename   -- expect false
#eval irAlphaCheckBlock sample alphaRename     -- expect true
/-! ### 10. The immutable-key tie, made decidable -/

/-- **THE TIE, DECIDABLE.** 'ShellModel.vkImmutableKey' and 'quotientImmutableKey' are the keys the
    model reads; 'DeploymentW.vkImm' and 'qImm' pin the keys the DEPLOYMENT promises, written as
    literals inside their own statements. Until this line the tie between the two was prose:
    swapping the two constants' definitions left every gate in the tree green, because every gate
    read the constants - 'ShellModel.bindLocals_keys_are_the_pinned_ones' compares the model's own
    block against those same two constants, so a swap moves both sides together. These three read
    the LITERALS, so a swap reddens them, and the theorem below stops elaborating. -/
def vkKeyTie : Bool :=
  EVM.litValue (.string vkImmutableKey) == EVM.litValue (.string "AUTHORIZED_VK")

def qKeyTie : Bool :=
  EVM.litValue (.string quotientImmutableKey) == EVM.litValue (.string "AUTHORIZED_QUOTIENT")

/-- The two keys are distinct, which is what makes a SWAP of them visible rather than harmless. -/
def keysDistinct : Bool := vkImmutableKey ≠ quotientImmutableKey

/-- **THE TIE AS A THEOREM.** 'DeploymentW.vkImm' is about the key the model actually reads. Swap
    the definitions of 'vkImmutableKey' and 'quotientImmutableKey' in ShellModel.lean and the
    'show' below stops elaborating: the build reddens, not just a gate. This is the R-58
    copy-without-a-pin class closed at the end the previous package handed over as undecidable. -/
theorem model_vk_read_is_the_pinned_address {S : Surface p G₁ G₂ Gₜ} {W : ExecEnv}
    {H : Midfall.Halo2.Hash} {vkAddr quotientAddr : U256}
    (D : DeploymentW S W H vkAddr quotientAddr) (h : S.expectedVkCodehash.isSome) :
    S.shellLayout.immutable (EVM.litValue (.string vkImmutableKey)) = vkAddr := by
  show S.shellLayout.immutable (EVM.litValue (.string "AUTHORIZED_VK")) = vkAddr
  exact D.vkImm h

/-- The quotient twin: same shape, same consequence. -/
theorem model_quotient_read_is_the_pinned_address {S : Surface p G₁ G₂ Gₜ} {W : ExecEnv}
    {H : Midfall.Halo2.Hash} {vkAddr quotientAddr : U256}
    (D : DeploymentW S W H vkAddr quotientAddr) (h : S.quotientRuntime.isSome) :
    S.shellLayout.immutable (EVM.litValue (.string quotientImmutableKey)) = quotientAddr := by
  show S.shellLayout.immutable (EVM.litValue (.string "AUTHORIZED_QUOTIENT")) = quotientAddr
  exact D.qImm h

#eval vkKeyTie && qKeyTie && keysDistinct   -- expect true
#print axioms Midfall.Yul.IRCheck.irCheckCore_sound
#print axioms Midfall.Yul.IRCheck.irCheck_sound
#print axioms Midfall.Yul.IRCheck.planted_rename_fails_alpha
#print axioms Midfall.Yul.IRCheck.model_vk_read_is_the_pinned_address
end Midfall.Yul.IRCheck
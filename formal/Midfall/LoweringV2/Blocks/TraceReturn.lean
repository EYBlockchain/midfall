/-
  Midfall.LoweringV2.Blocks.TraceReturn

  T.1 (SEM / SKELETON): ONE TACTIC INTERFACE FOR THE V2 BLOCK CONTRACTS, AND THE SMALLEST OF THE
  THREE NAMED CONE NODES HAND-PROVED AGAINST IT.

  THE THREE NODES THE CARD NAMED, AND WHICH ONE THIS FILE CLOSES.
  1. TraceReturn BlockSound / BlockProgress - the §6 shapes at Blocks.lean:92 / :106;
  2. ec_pairing_contract - FP.0's, FinalPairing.lean:314;
  3. the loop-bearing node, which M0.1 measured to be lagrange through batch_invert.
  Node 1 is the smallest by a wide margin and is the one closed here: R.slice .traceReturn is
  THREE statements with no bindings (GenAst.emitTraceReturnBlock), it calls no precompile on the
  clean path, it has no loop, and - unlike ec_pairing_contract - its post names no Inv at all, so
  the Inv .pcs -> Inv .pairing transfer that FP.0 measured past the 200 000-heartbeat default never
  enters. Node 2 needs staticcall stepping plus fpG2Slots; node 3 needs fuel and a loop invariant.
  Both stay open and are handed to T.4 and T.3 with the interface below.

  WHAT THE INTERFACE IS. SIX named step lemmas, S1-S6, each stated at the generality the OTHER two
  nodes need and not just what TraceReturn uses: an arbitrary function environment, an arbitrary
  statement body, and an address expression left SYMBOLIC because the constant inliner leaves it
  symbolic (§1). S1-S5 are §2, S6 is §3. They are a lemma family and a call pattern, not a macro:
  packaging them into one tactic is T.2's job, and the cards now say which of the six each card calls.
  THE CALL PATTERN, in order, for a straight-line slice: S1 puts the slice into statement-list form;
  then at each statement, S3 (rcases Step.stmts_cons_inv) splits the run and an inversion lemma
  (S2/S4/S5/S6) consumes the head, with the seqStop branch closed by the outcome lemma of the same
  step. The walk ends when the last statement's inversion produces the halt record §6's post names.

  THE FINDING THAT COST THE MOST, AND IS THE CARD'S REAL OUTPUT: THE SLICE DOES NOT REDUCE BY simp.
  Render.slice q is Inline.inlineContractConstants R.consts (GenAst.emitPartial pv q) and the
  inliner is a fuel-64 fold, so the emitted arm does NOT unfold under simp/unfold (measured: unfold
  Inline.inlineScan strands the goal inside the equation-compiler's brecOn, and simp only
  [inlineScan.eq_1, eq_2] cannot rewrite the partially-applied recursive argument). What DOES work,
  in three moves: show the inlined form, rfl the fold at a goal whose stuck subterms are named by
  explicit defs (trRetExpr and friends), then rewrite the one lookup that must not be stuck. That is
  tr_slice, and every block card needs it.

  A SECOND FINDING, CHEAPER BUT SURPRISING: the inlined fail helper IS reachable. The FP.0 header
  warns that reducing hoist over the whole inlined helper block is the 18-minute / 8.7 GB class of
  lemma. It is not, for a lookupFun: hoist is a top-level filterMap and lookupFun short-circuits, so
  fail_lookup is rfl and this whole file elaborates in seconds under the default budget. No
  heartbeat was raised and nothing here exceeded 60 s.

  PREMISE GAP FOUND (reported, not worked around): THE EXISTENCE HALF NEEDS THE RETURN WINDOW.
  BlockProgress is TOTAL (StmtsTotal = StmtsContract /\ StmtsContractAll), so it must EXHIBIT a run,
  and a run of the terminal arm needs a value for the inlined RETURN_MPTR site. If the render's
  constant table binds it, the site is a literal and there is no side condition; if it does not, the
  site is the free variable RETURN_MPTR and the caller's VEnv must bind it - and NOTHING in Frame,
  Clean or Inv binds it. v1 recorded the same trap at Partials.lean:1251 ("RETURN_MPTR and
  ERR_PROOF_REJECTED are FREE identifiers of the fragment, so the arm has no run at all unless the
  caller's VEnv binds RETURN_MPTR, and the spec is satisfied vacuously at every environment that does
  not"). V2's Render.Valid pins only TRANSCRIPT_MPTR (Statements.lean:169). So the existence half is
  stated under the named pin trRetMptr, which is a computation at any real deployment
  (pinnedConstants has ("RETURN_MPTR", 4096), InlineConstants.lean:149) and is NOT assumed for free:
  the forall-runs halves - BlockSound, both directions - need no such hypothesis, because there the
  run is a hypothesis and the binding is a CONSEQUENCE of it (trAddr, §1). That asymmetry - soundness
  free, existence pinned - is the finding.

  BRIDGE-DIRECTION CHECK (the card asked; the answer is NO): none of halted_of_view_eq,
  worldEq_of_view_eq or view_eq_of_worldEq_and_halt is cited anywhere in this file, and none is
  needed. Every step here is a Step INVERSION on a run hypothesis, which is the direction the §6
  contracts are stated in; the view lemmas transport an OBSERVATION, and this node never leaves the
  run level. C.2's warning that the named view lemmas point the wrong way for composition does not
  bite here, and Run_worldEq_of_noWriters (the registered sorry at Bridge.lean:1221) is untouched.

  NO sorry IN THIS FILE. Partial has no ToString and poseidonRender is noncomputable, so nothing here
  computes on a render: the slice shape came from rfl on the emitter, not from #eval.
-/
import Midfall.LoweringV2.Blocks

namespace Midfall.LoweringV2.Blocks.TraceReturn

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]
  {c : ExternalCalls} {g : ExternalGas}

/-! ## 1. INTERFACE STEP 1: put the slice into statement-list form

  The three identifiers the TraceReturn arm mentions, as the constant inliner leaves them. They are
  DEFINED rather than hypothesised away because the inliner's output is stuck on a symbolic table:
  RETURN_MPTR and ERR_PROOF_REJECTED stay as a match on the lookup, and success is filtered out of
  every render's table (constTableOf drops it) so its site always reduces to the variable. -/

/-- The inlined RETURN_MPTR use site of the terminal arm. -/
def trRetExpr (consts : Inline.Consts) : Expr EVM.Op :=
  match consts.lookup "RETURN_MPTR" with
  | some v => Expr.lit (.number v)
  | none => Expr.var "RETURN_MPTR"

/-- The inlined ERR_PROOF_REJECTED use site, the argument of the fail call the guard makes. -/
def trErrExpr (consts : Inline.Consts) : Expr EVM.Op :=
  match consts.lookup "ERR_PROOF_REJECTED" with
  | some v => Expr.lit (.number v)
  | none => Expr.var "ERR_PROOF_REJECTED"

/-- The inlined success use site - always the variable, by consts_succ_none. -/
def trSuccExpr (consts : Inline.Consts) : Expr EVM.Op :=
  match consts.lookup "success" with
  | some v => Expr.lit (.number v)
  | none => Expr.var "success"

/-- A table that binds no pair named x does not resolve lookup x. -/
theorem lookup_none_of_ne (x : String) (l : List (String × Nat))
    (h : ∀ y ∈ l, y.1 ≠ x) : List.lookup x l = none := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      rcases h y (List.Mem.head _) with hy
      rw [List.lookup]
      split
      · simp_all
      · exact ih (fun z hz => h z (List.Mem.tail _ hz))

/-- **THE success SITE IS NEVER A LITERAL.** constTableOf filters vk and success out of the table
    precisely so the two shell locals stay locals (Program.lean:60). This is the lookup the slice
    equation has to rewrite away, and the reason the guard guards a VARIABLE. -/
theorem consts_succ_none (R : Render p G₁ G₂ Gₜ) : R.consts.lookup "success" = none :=
  lookup_none_of_ne "success" _ (by
    intro x hx
    rcases List.mem_filter.mp hx with ⟨_, h2⟩
    simp at h2
    exact h2.2)

/-- The fold, at a table left symbolic. This is the rfl the unfold/simp route could not reach: the
    three stuck sites are named by the defs above, so the kernel closes the gap. -/
theorem tr_slice_raw (consts : Inline.Consts) :
    Inline.inlineContractConstants consts Midfall.Lowering.GenAst.emitTraceReturnBlock =
      [Stmt.cond (Expr.builtin Op.iszero [trSuccExpr consts])
          [Stmt.exprStmt (Expr.call "fail" [trErrExpr consts])],
        Stmt.exprStmt (Expr.builtin Op.mstore [trRetExpr consts, Expr.lit (.number 1)]),
        Stmt.exprStmt (Expr.builtin Op.ret [trRetExpr consts, Expr.lit (.number 0x20)])] := rfl

/-- **INTERFACE STEP 1 - yul_slice.** The TraceReturn slice as a three-statement list. The same
    three moves (show the inlined form, rfl against the stuck-site defs, rewrite the one lookup that
    must reduce) are what every other block card needs; only the right-hand side changes. -/
theorem tr_slice (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.traceReturn =
      [Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
          [Stmt.exprStmt (Expr.call "fail" [trErrExpr R.consts])],
        Stmt.exprStmt (Expr.builtin Op.mstore [trRetExpr R.consts, Expr.lit (.number 1)]),
        Stmt.exprStmt (Expr.builtin Op.ret [trRetExpr R.consts, Expr.lit (.number 0x20)])] := by
  classical
  show Inline.inlineContractConstants R.consts Midfall.Lowering.GenAst.emitTraceReturnBlock = _
  rw [tr_slice_raw]
  simp only [trSuccExpr, consts_succ_none R]

/-- The address the terminal arm returns from, in the one form that works in BOTH cases of the
    inlined site: the constant table if it binds RETURN_MPTR, otherwise whatever the caller's VEnv
    binds. Reading it off the environment rather than assuming it is what keeps BlockSound free of a
    side condition - a run existing is what proves the address has a value. -/
def trAddr (R : Render p G₁ G₂ Gₜ) (V : VEnv (Bridge.Dialect c g)) : Option U256 :=
  match R.consts.lookup "RETURN_MPTR" with
  | some v => some (BitVec.ofNat 256 v)
  | none => VEnv.get V "RETURN_MPTR"

/-- The dialect's literal map, pinned once: a decimal literal is the 256-bit word. -/
theorem tr_lit_number (v : Nat) :
    (Bridge.Dialect c g).litValue (Literal.number v) = BitVec.ofNat 256 v := rfl

/-- The inlined return site is a literal or a variable, so it NEVER HALTS. Two of the Step rules for
    an expression sequence (builtinArgsHalt, argsRestHalt / argsHeadHalt) would otherwise have to be
    argued away at every use site; naming the fact once is what keeps the walk lemmas short. -/
theorem trRet_ne_halts {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (trRetExpr R.consts) (.halt st₂)) : False := by
  classical
  cases hmv : R.consts.lookup "RETURN_MPTR" with
  | some v =>
      rw [show trRetExpr R.consts = Expr.lit (.number v) from by simp [trRetExpr, hmv]] at h
      cases h
  | none =>
      rw [show trRetExpr R.consts = Expr.var "RETURN_MPTR" from by simp [trRetExpr, hmv]] at h
      cases h

/-- A one-literal argument list never halts either (the size operand of mstore / ret). -/
theorem trArgs_lit_ne_halts {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState} {n : Nat}
    (h : Step (Bridge.Dialect c g) funs V st
      (Code.args [Expr.lit (.number n)]) (.eres (.halt st₂))) : False := by
  cases h with
  | argsRestHalt h' => cases h'
  | argsHeadHalt _ h' => cases h'

/-- The two shapes of the inlined site, reconciled: an evaluation of trRetExpr pins trAddr and
    leaves the state alone. This is the lemma that lets a walk treat the site as OPAQUE - the case
    split on the lookup happens once, here, instead of at every use site. -/
theorem trRet_eval_inv {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState} {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (trRetExpr R.consts) (.vals [a] st₂)) :
    trAddr R V = some a ∧ st₂ = st := by
  classical
  cases hmv : R.consts.lookup "RETURN_MPTR" with
  | some v =>
      rw [show trRetExpr R.consts = Expr.lit (.number v) from by simp [trRetExpr, hmv]] at h
      cases h with
      | lit => refine ⟨by rw [trAddr, hmv, tr_lit_number], rfl⟩
  | none =>
      rw [show trRetExpr R.consts = Expr.var "RETURN_MPTR" from by simp [trRetExpr, hmv]] at h
      cases h with
      | var hget => refine ⟨by simpa [trAddr, hmv] using hget, rfl⟩

/-- The pin-free half of the previous lemma, for a walk that only needs the address. -/
theorem trRet_val {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V : VEnv (Bridge.Dialect c g)} {st st₂ : EvmState} {a : U256}
    (h : EvalExpr (Bridge.Dialect c g) funs V st (trRetExpr R.consts) (.vals [a] st₂)) :
    trAddr R V = some a := (trRet_eval_inv h).1

/-- **THE PIN THE EXISTENCE HALF NEEDS** (header: PREMISE GAP). The render's table binds the return
    window, so the terminal arm has a run at ANY environment. A computation at a real deployment,
    never a free hypothesis: pinnedConstants has ("RETURN_MPTR", 4096). -/
def trRetMptr (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ m, R.consts.lookup "RETURN_MPTR" = some m

/-- Under the pin, trAddr is the literal and needs nothing from the environment. -/
theorem trAddr_of_trRetMptr {R : Render p G₁ G₂ Gₜ} (h : trRetMptr R)
    (V : VEnv (Bridge.Dialect c g)) : ∃ a, trAddr R V = some a := by
  obtain ⟨m, hm⟩ := h
  exact ⟨BitVec.ofNat 256 m, by simp [trAddr, hm]⟩

/-! ## 2. THE RECURRING STEP LEMMAS

  Six, in the order a walk uses them. Each is dialect-fixed at Bridge.Dialect c g (the only dialect
  §6 runs blocks in) and general in everything else: the function environment, the statement body,
  the address. That generality is the point - T.4's staticcall walk and T.3's loop walk re-use the
  same six against a different slice. -/

/-- **INTERFACE STEP 2 - the guard expression has exactly one value.** Inverted directly through
    stepOp, NOT through Bridge.dialect_deterministic (still a registered hole): iszero is a local
    operation, so uniqueness is free. Copied in shape from v1's eval_iszero_success
    (Partials.lean:895), which this file may not import. -/
theorem tr_iszero_val {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {r : EResult (Bridge.Dialect c g)}
    (hs : VEnv.get V "success" = some (1 : U256))
    (h : EvalExpr (Bridge.Dialect c g) funs V st
      (Expr.builtin Op.iszero [Expr.var "success"]) r) : r = .vals [0] st := by
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

/-- **INTERFACE STEP 3 - yul_split at the guard: the guard skips.** General in the body: on the
    clean path the fail arm is never entered, so what it contains does not matter and this lemma
    never mentions it. That is what makes the soundness half cheap, and it is the shape T.5's guard
    step reuses at .finalPairing. -/
theorem tr_guard_skip {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)}
    {st : EvmState} {body : Block EVM.Op}
    (hs : VEnv.get V "success" = some (1 : U256))
    {V' : VEnv (Bridge.Dialect c g)} {st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
      (Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"]) body) V' st' o) :
    V' = V ∧ st' = st ∧ o = .normal := by
  cases h with
  | ifTrue hc hnz _ =>
      have h0 := tr_iszero_val hs hc
      cases h0
      exact absurd rfl hnz
  | ifFalse hc _ =>
      have h0 := tr_iszero_val hs hc
      cases h0
      exact ⟨rfl, rfl, rfl⟩
  | ifHalt hc =>
      have h0 := tr_iszero_val hs hc
      cases h0

/-- **INTERFACE STEP 4 - a word store, inverted.** The environment is untouched, the outcome is
    normal, and the state is exactly the word write at the address trAddr names. THE INDEX TRICK:
    the outcome is part of the Step index, so stating the hypothesis at .normal makes cases prune
    the halting rule for free - no builtinArgsHalt / builtinHalt branch to argue away. And the
    address is NOT cased on: trRet_eval_inv absorbs the two shapes of the inlined site, which is
    what lets one lemma serve both a bound and an unbound constant table. -/
theorem tr_mstore_step {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.mstore
          [trRetExpr R.consts, Expr.lit (.number 1)])) V' st' .normal) :
    ∃ a, trAddr R V = some a ∧ V' = V ∧
      st' = { touchMemory st a.toNat 32 with memory := storeWord st.memory a.toNat 1 } := by
  cases h with
  | exprStmt hex =>
      cases hex with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hnil hvar =>
              cases hnil with
              | argsCons hnil2 hvar2 =>
                  cases hnil2 with
                  | argsNil =>
                      cases hvar2 with
                      | lit =>
                          rename_i st₁ v
                          obtain ⟨haddr, hst⟩ := trRet_eval_inv hvar
                          refine ⟨v, haddr, rfl, ?_⟩
                          have h4 : (Bridge.Dialect c g).Builtin Op.mstore [v, (1 : U256)] st
                            (.ok [] st') := by
                            rw [← hst]; exact hbi
                          simp only [Bridge.Dialect, builtinWithExternal, stepOp] at h4
                          rw [Option.some.injEq, BuiltinResult.ok.injEq] at h4
                          exact h4.2.symm

/-- **INTERFACE STEP 5 - the return record.** The halt payload is readBytes over the address the
    store wrote, so the post can name abiTrue without naming the address. Same index trick at .halt;
    the two occurrences of the site are reconciled by trAddr, which is why the caller can hand in the
    address the mstore step produced. -/
theorem tr_ret_step {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {a : U256}
    (ha : trAddr R V = some a)
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.ret
          [trRetExpr R.consts, Expr.lit (.number 0x20)])) V' st' .halt) :
    V' = V ∧ st'.halted = some (.ret, readBytes st.memory a.toNat 32) := by
  cases h with
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hnil hvar =>
              cases hnil with
              | argsCons hnil2 hvar2 =>
                  cases hnil2 with
                  | argsNil =>
                      cases hvar2 with
                      | lit =>
                          rename_i st₁ v
                          obtain ⟨haddr, hst⟩ := trRet_eval_inv hvar
                          rw [haddr] at ha; cases ha
                          refine ⟨rfl, ?_⟩
                          have h4 : (Bridge.Dialect c g).Builtin Op.ret [a, (32 : U256)] st
                            (.halt st') := by
                            rw [← hst]; exact hbi
                          simp only [Bridge.Dialect, builtinWithExternal, stepOp] at h4
                          rw [Option.some.injEq, BuiltinResult.halt.injEq] at h4
                          rw [← h4]
                          rfl
      | builtinArgsHalt hargs => cases hargs with
        | argsRestHalt h => exact (trArgs_lit_ne_halts h).elim
        | argsHeadHalt _ h => exact (trRet_ne_halts h).elim

/-- The memory fact the post needs: the 32 bytes an mstore of the word 1 wrote, read back, ARE
    abiTrue, independent of the address and of the prior memory. Copied from v1
    (Partials.lean:1080); that module is retired and may not be imported. -/
theorem map_congr_range {β : Type} (n : Nat) (f g : Nat → β) (h : ∀ i, i < n → f i = g i) :
    (List.range n).map f = (List.range n).map g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      rw [ih (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ n)))]
      rw [List.map_singleton, List.map_singleton, h n (Nat.lt_succ_self n)]

theorem readBytes_storeWord_one (mem : Nat → UInt8) (p : Nat) :
    readBytes (storeWord mem p 1) p 32 = abiTrue := by
  have pt : ∀ i, i < 32 → storeWord mem p 1 (p + i) = byteAt (1 : U256) (31 - i) := by
    intro i hi
    show (if p ≤ p + i ∧ p + i < p + 32 then byteAt (1 : U256) (31 - (p + i - p))
      else mem (p + i)) = byteAt (1 : U256) (31 - i)
    simp [hi]
  have key : (List.range 32).map (fun i => storeWord mem p 1 (p + i))
      = (List.range 32).map (fun i => byteAt (1 : U256) (31 - i)) := map_congr_range 32 _ _ pt
  have tail : (List.range 32).map (fun i => byteAt (1 : U256) (31 - i)) = abiTrue := by decide
  show (List.range 32).map (fun i => storeWord mem p 1 (p + i)) =
    (Midfall.natToBytesBE 1 32).data.toList
  rw [key, tail]
  rfl


/-! ## 3. INTERFACE STEP 6 - the fail helper, PARTLY stepped

  The revert arm of every block contract in §6 comes from fail(sel), so what is proved here is stated
  for the helper as the render hoists it, not for TraceReturn's guard: T.5's fp_stmt_steps needs the
  same facts at .finalPairing with a different selector, and they are the ONLY thing there. TWO facts
  are delivered: fail_lookup (the scope resolves the name, by rfl) and revertedOf_revert (a revert
  record is Reverted, whatever the payload). THE THIRD - tr_fail_reverts, the inversion of the call
  itself - is NOT finished here, and that is the one gap that keeps BlockSound's second conjunct open.
  The exact state it stops at, and the case-name work left, are written into T.5's card so the next
  card does not rediscover them. Note what the shape does NOT need: the selector value. fail writes
  shl(224, sel) at 0x00 and reverts four bytes, so the halt record is a revert whatever sel is - which
  is why the inlined ERR_PROOF_REJECTED site, like the return window, never needs to be resolved. -/

/-- The fail definition, as the render's own scope resolves it. rfl: hoist is a top-level filterMap
    and lookupFun short-circuits, so the whole inlined helper block is never normalised to the last
    statement - the FP.0 warning about an 18-minute reduction does not apply here. -/
theorem fail_lookup (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    lookupFun (R.scope c g) "fail" =
      some ({ params := ["sel"], rets := [],
              body := [Stmt.exprStmt (Expr.builtin Op.mstore
                  [Expr.lit (.number 0),
                   Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
                Stmt.exprStmt (Expr.builtin Op.revert
                  [Expr.lit (.number 0), Expr.lit (.number 4)])] },
            R.scope c g) := rfl

/-- A halt record whose kind is revert is a Reverted state, whatever the payload bytes. -/
theorem revertedOf_revert {st : EvmState} {d : List UInt8} (h : st.halted = some (.revert, d)) :
    Reverted st := by
  simp [Reverted, revertedOf, h]

/-- **A word store never halts: its outcome is normal.** Stated as an outcome equality rather than a
    negation because a walk meets it in the seqStop branch of a split, where the outcome is a variable
    and the hypothesis is o ≠ normal - so the walk needs the equality to contradict it, not a False. -/
theorem tr_mstore_o {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.mstore
          [trRetExpr R.consts, Expr.lit (.number 1)])) V' st' o) : o = .normal := by
  cases h with
  | exprStmt _ => rfl
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs hbi =>
          cases hargs with
          | argsCons hnil hvar =>
              cases hnil with
              | argsCons hnil2 hvar2 =>
                  cases hnil2 with
                  | argsNil =>
                      cases hvar2 with
                      | lit =>
                          rename_i st₁ v
                          have h4 : (Bridge.Dialect c g).Builtin Op.mstore [v, (1 : U256)] st₁
                            (.halt st') := hbi
                          simp [Bridge.Dialect, builtinWithExternal, stepOp] at h4
      | builtinArgsHalt hargs => cases hargs with
        | argsRestHalt h => exact (trArgs_lit_ne_halts h).elim
        | argsHeadHalt _ h => exact (trRet_ne_halts h).elim

/-- **A return always halts: its outcome is halt.** Same shape as the store lemma. -/
theorem tr_ret_o {R : Render p G₁ G₂ Gₜ} {funs : FunEnv (Bridge.Dialect c g)}
    {V V' : VEnv (Bridge.Dialect c g)} {st st' : EvmState} {o : Outcome}
    (h : ExecStmt (Bridge.Dialect c g) funs V st
        (Stmt.exprStmt (Expr.builtin Op.ret
          [trRetExpr R.consts, Expr.lit (.number 0x20)])) V' st' o) : o = .halt := by
  cases h with
  | exprStmtHalt hex =>
      cases hex with
      | builtinHalt hargs hbi => rfl
      | builtinArgsHalt hargs => cases hargs with
        | argsRestHalt h => exact (trArgs_lit_ne_halts h).elim
        | argsHeadHalt _ h => exact (trRet_ne_halts h).elim
  | exprStmt hex =>
      cases hex with
      | builtinOk hargs hbi =>
          cases hargs with
          | argsCons hnil hvar =>
              cases hnil with
              | argsCons hnil2 hvar2 =>
                  cases hnil2 with
                  | argsNil =>
                      cases hvar2 with
                      | lit =>
                          rename_i st₁ v
                          have h4 : (Bridge.Dialect c g).Builtin Op.ret [v, (32 : U256)] st₁
                            (.ok [] st') := hbi
                          simp [Bridge.Dialect, builtinWithExternal, stepOp] at h4

/-! ## 4. THE NODE, CLOSED

  WHAT IS CLOSED HERE: BlockProgress R .traceReturn - §6's TOTAL contract (Blocks.lean:106), both
  halves, sorry-free - and BlockSound's FIRST conjunct (Blocks.lean:92), as tr_sound_clean. BlockSound's
  second conjunct (the poisoned walk) is NOT closed: its only content is the fail inversion of §3, and
  the case-name work is recorded in T.5's card rather than guessed at here.

  What the clean walk spends: q.pre is .pairing, so the clean boundary is Clean R .pairing - and the
  ONLY part of it used is VEnv.get V "success" = some 1, the third conjunct of Clean. No Inv clause is
  read and no Frame field is preserved: the terminal arm writes one word and returns, and exitOk for
  .traceReturn names a halt record rather than a checkpoint. That is the whole reason this is the
  smallest of the three nodes, and why the Inv .pcs -> Inv .pairing transfer never appears. -/

abbrev Dperm (product : PairingProduct) (g : ExternalGas) :=
  Bridge.Dialect (permissive (callsOf product)) g

/-- **TRACERETURN'S SOUNDNESS CONTRACT, CONJUNCT 1.** From a clean boundary the run reverts, or takes
    the exitOk arm: a returning halt whose payload is abiTrue. -/
theorem tr_sound_clean (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas)
    {V : VEnv (Dperm product g)} {st : EvmState}
    (hclean : Clean R Checkpoint.pairing Snap H vkAddr cd V st)
    {V' : VEnv (Dperm product g)} {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Dperm product g) (R.scope (permissive (callsOf product)) g) V st
      (R.slice Partial.traceReturn) V' st' o) :
    (o = .halt ∧ Reverted st') ∨
      exitOk R Partial.traceReturn Snap H vkAddr cd V' st' o ∨
      (o = .normal ∧ Poisoned R H vkAddr cd V' st') := by
  rw [tr_slice R] at hrun
  have hsucc : VEnv.get V "success" = some (1 : U256) := hclean.2.2
  rcases Step.stmts_cons_inv (D := Dperm product g) hrun with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · obtain ⟨rfl, rfl, _⟩ := tr_guard_skip hsucc h₁
    rcases Step.stmts_cons_inv (D := Dperm product g) hrest with
        ⟨V₂, st₂, h₂, hlast⟩ | ⟨h₂, hne₂⟩
    · obtain ⟨a, haddr, rfl, hst₂⟩ := tr_mstore_step h₂
      rw [hst₂] at hlast
      rcases Step.stmts_cons_inv (D := Dperm product g) hlast with
          ⟨V₃, st₃, h₃, hnil⟩ | ⟨h₃, hne₃⟩
      · have h0 := tr_ret_o h₃
        cases h0
      · have ho : o = Outcome.halt := tr_ret_o h₃
        subst ho
        obtain ⟨rfl, hrec⟩ := tr_ret_step haddr h₃
        have hpay : some (HaltKind.ret, readBytes (storeWord st₁.memory (BitVec.toNat a) 1)
            (BitVec.toNat a) 32) = some (HaltKind.ret, abiTrue) :=
          congrArg (fun x => some (HaltKind.ret, x)) (readBytes_storeWord_one _ _)
        exact Or.inr (Or.inl ⟨rfl, hrec.trans hpay⟩)
    · exact absurd (tr_mstore_o h₂) hne₂
  · obtain ⟨_, _, h3⟩ := tr_guard_skip hsucc h₁
    exact absurd h3 hne


/-- The honest dialect BlockProgress runs at, and its scope. -/
abbrev Dhonest (product : PairingProduct) :=
  Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)

/-- **TRACERETURN'S PROGRESS, FORALL-RUNS HALF.** Every honest run exits the traceReturn way. Same
    walk as tr_sound_clean, with the two impossible arms of §6's soundness post dropped because the
    honest dialect cannot revert here: the guard skips and the terminal statement halts. -/
theorem tr_progress_all (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {V : VEnv (Dhonest product)} {st : EvmState}
    (hclean : Clean R Checkpoint.pairing Snap H vkAddr cd V st)
    {V' : VEnv (Dhonest product)} {st' : EvmState} {o : Outcome}
    (hrun : ExecStmts (Dhonest product) (R.scope (callsOf product)
        (ExternalGas.ofFun fun _ => 0)) V st (R.slice Partial.traceReturn) V' st' o) :
    exitOk R Partial.traceReturn Snap H vkAddr cd V' st' o := by
  classical
  rw [tr_slice R] at hrun
  have hsucc : VEnv.get V "success" = some (1 : U256) := hclean.2.2
  rcases Step.stmts_cons_inv (D := Dhonest product) hrun with ⟨V₁, st₁, h₁, hrest⟩ | ⟨h₁, hne⟩
  · obtain ⟨rfl, rfl, _⟩ := tr_guard_skip hsucc h₁
    rcases Step.stmts_cons_inv (D := Dhonest product) hrest with
        ⟨V₂, st₂, h₂, hlast⟩ | ⟨h₂, hne₂⟩
    · obtain ⟨a, haddr, rfl, hst₂⟩ := tr_mstore_step h₂
      rw [hst₂] at hlast
      rcases Step.stmts_cons_inv (D := Dhonest product) hlast with
          ⟨V₃, st₃, h₃, hnil⟩ | ⟨h₃, hne₃⟩
      · have h0 := tr_ret_o h₃
        cases h0
      · have ho : o = Outcome.halt := tr_ret_o h₃
        subst ho
        obtain ⟨rfl, hrec⟩ := tr_ret_step haddr h₃
        have hpay : some (HaltKind.ret, readBytes (storeWord st₁.memory (BitVec.toNat a) 1)
            (BitVec.toNat a) 32) = some (HaltKind.ret, abiTrue) :=
          congrArg (fun x => some (HaltKind.ret, x)) (readBytes_storeWord_one _ _)
        exact ⟨rfl, hrec.trans hpay⟩
    · exact absurd (tr_mstore_o h₂) hne₂
  · obtain ⟨_, _, h3⟩ := tr_guard_skip hsucc h₁
    exact absurd h3 hne

/-- **TRACERETURN'S PROGRESS, EXISTENCE HALF** - under the trRetMptr pin, for the reason the header
    gives: the run must be EXHIBITED, and an exhibition needs the return window bound. Built
    statement by statement from the Step constructors, which is the forward dual of the §2 inversions
    and uses the same six facts. -/
theorem tr_progress_ex (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hpin : trRetMptr R)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {V : VEnv (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))} {st : EvmState}
    (hclean : Clean R Checkpoint.pairing Snap H vkAddr cd V st) :
    ∃ V' st' o, ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)) (R.scope (callsOf product)
        (ExternalGas.ofFun fun _ => 0)) V st (R.slice Partial.traceReturn) V' st' o ∧
      exitOk R Partial.traceReturn Snap H vkAddr cd V' st' o := by
  obtain ⟨m, hm⟩ := hpin
  have hsucc : VEnv.get V "success" = some (1 : U256) := hclean.2.2
  have hsite : trRetExpr R.consts = Expr.lit (.number m) := by simp [trRetExpr, hm]
  set a : U256 := BitVec.ofNat 256 m with ha
  set st₁ : EvmState := { touchMemory st a.toNat 32 with memory := storeWord st.memory a.toNat 1 }
  set st₂ : EvmState := { touchMemory st₁ a.toNat 32 with
    halted := some (HaltKind.ret, readBytes st₁.memory a.toNat 32) }
  have hX : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (trRetExpr R.consts) (.vals [a] st) := by
    rw [hsite]
    exact Step.lit
  have hX1 : EvalExpr (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st₁
      (trRetExpr R.consts) (.vals [a] st₁) := by
    rw [hsite]
    exact Step.lit
  have hz : (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.iszero [1] st (.ok [0] st) := by
    show (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.iszero [(1 : U256)] st (.ok [0] st)
    rfl
  have hmsbi : (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.mstore [a, 1] st (.ok [] st₁) := by
    show (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.mstore [(BitVec.ofNat 256 m), (1 : U256)] st (.ok [] st₁)
    rfl
  have hretbi : (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.ret [a, 32] st₁ (.halt st₂) := by
    show (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0)).Builtin Op.ret [(BitVec.ofNat 256 m), (32 : U256)] st₁ (.halt st₂)
    rfl
  have hwalk : ExecStmts (Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope (callsOf product) (ExternalGas.ofFun fun _ => 0)) V st
      (R.slice Partial.traceReturn) V st₂ .halt := by
    rw [tr_slice R]
    refine Step.seqCons (Step.ifFalse
      (Step.builtinOk (Step.argsCons Step.argsNil (Step.var hsucc)) hz) rfl) ?_
    refine Step.seqCons (Step.exprStmt
      (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hX) hmsbi)) ?_
    exact Step.seqStop (Step.exprStmtHalt
      (Step.builtinHalt (Step.argsCons (Step.argsCons Step.argsNil Step.lit) hX1) hretbi))
      (by simp)
  refine ⟨V, st₂, .halt, hwalk, ⟨rfl, ?_⟩⟩
  show some (HaltKind.ret, readBytes st₁.memory a.toNat 32) = some (HaltKind.ret, abiTrue)
  rw [show st₁.memory = storeWord st.memory a.toNat 1 from rfl, readBytes_storeWord_one]

/-- **NODE 1 CLOSED, HALF 2 OF 2: BlockProgress R .traceReturn**, i.e. §6's TOTAL contract - a run
    exists, and every run is good. -/
theorem tr_blockProgress (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hpin : trRetMptr R)
    (Snap : Snapshot p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) :
    BlockProgress R Partial.traceReturn Snap H vkAddr product cd :=
  ⟨fun V st h => tr_progress_ex R product hpin Snap H vkAddr cd h,
   fun V st h V' st' o hrun => tr_progress_all R product Snap H vkAddr cd h hrun⟩

end Midfall.LoweringV2.Blocks.TraceReturn

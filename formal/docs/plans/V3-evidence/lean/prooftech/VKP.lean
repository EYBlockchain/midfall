import WPTac
import WPX
import Midfall.LoweringV2.Blocks.VkLoading
set_option autoImplicit false

/-!
VKP (scratch, prooftech, card GEN.0): the vkLoading block for EVERY render - the constant table,
the function scope and (later, `LoopRule.lean`) loop bounds are variables.

CONSTANT NAMES `vkBody` LOOKS UP THROUGH `vkSite` (READ: `Blocks/VkLoading.lean:94-160`).
Seventeen names at twenty sites.

  name                         statement(s)            role
  ---------------------------  ----------------------  ------------------------------------------
  vk                           S1 (x2), S2             shell local: must NOT be bound (stays a var)
  success                      S3 (`vkSucc0`)          shell local: must NOT be bound (stays a var)
  EXPECTED_VK_LENGTH           S1                      extcodesize comparand
  EXPECTED_VK_CODEHASH_WORD    S1                      extcodehash comparand
  ERR_VK_MISMATCH              S1, S9                  selector passed to `fail`
  VK_MPTR                      S2                      extcodecopy destination
  EXPECTED_VK_PAYLOAD_LENGTH   S2                      extcodecopy length
  NUM_INSTANCES_MPTR           S3                      header slot (mload)
  K_MPTR                       S4                      header slot
  HAS_ACCUMULATOR_MPTR         S5                      header slot
  ACC_OFFSET_MPTR              S6                      header slot
  NUM_ACC_LIMBS_MPTR           S7                      header slot
  NUM_ACC_LIMB_BITS_MPTR       S8                      header slot
  PROOF_LEN_CPTR               S10                     calldataload offset
  NUM_INSTANCE_CPTR            S11                     calldataload offset
  INSTANCE_CPTR                S12                     calldatasize comparand base
  ERR_BAD_CALLDATA_SHAPE       S13                     selector passed to `fail`

FIFTEEN names must be bound (one `Nat` variable each) and TWO must be unbound. The GEN.0 card
expects "VK_MPTR, EXPECTED_VK_PAYLOAD_LENGTH, the six header slot names, the calldata constants":
it omits EXPECTED_VK_LENGTH, EXPECTED_VK_CODEHASH_WORD, ERR_VK_MISMATCH, ERR_BAD_CALLDATA_SHAPE.
The free variables are `Nat` (`Inline.Consts = List (String × Nat)`, `vkSite` emits
`Expr.lit (.number v)` with `v : Nat`), not `U256` as the card says.

SORRIES IN THIS FILE: ONE - `wpSS_exists_C` (§4), a STATEMENT for the existence half; it
generalises `wpSS_exists` (`WPX.lean:24`, itself a sorry). Everything else is proved, including
`vk_all_param` (no sorry at the normal exit, unlike the literal `vk_all`).
-/
namespace Midfall.Scratch.ProofTech
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall Midfall.Lowering Midfall.LoweringV2
open Midfall.LoweringV2.Blocks.TraceReturn Midfall.LoweringV2.Blocks.VkLoading

/-! ## 1. The parametric body with every constant site a literal of a free `Nat` -/

/-- A bound site is the table's literal. -/
theorem vkSite_lit {x : String} {consts : Inline.Consts} {v : Nat}
    (h : consts.lookup x = some v) : vkSite x consts = Expr.lit (.number v) := by
  simp only [vkSite, h]

/-- An unbound site is the variable. -/
theorem vkSite_var {x : String} {consts : Inline.Consts}
    (h : consts.lookup x = none) : vkSite x consts = Expr.var x := by
  simp only [vkSite, h]

/-- `vkBody` (`Blocks/VkLoading.lean:152`) with every constant site an `Expr.lit` of a free `Nat`
    and the two shell locals as variables. Argument order: the fifteen constants in the order of
    the table above, then `vkBody`'s own seven numerals. -/
def vkBodyV (vkLen vkHash errVk mVk payLen sN sK sA sO sL sB cPL cNI cI errCd : Nat)
    (n k w o l b q : Nat) : List (Stmt EVM.Op) :=
  [ Stmt.cond
      (Expr.builtin Op.iszero [Expr.builtin Op.and
        [Expr.builtin Op.eq [Expr.builtin Op.extcodesize [Expr.var "vk"],
                             Expr.lit (.number vkLen)],
         Expr.builtin Op.eq [Expr.builtin Op.extcodehash [Expr.var "vk"],
                             Expr.lit (.number vkHash)]]])
      [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errVk)])],
    Stmt.exprStmt (Expr.builtin Op.extcodecopy [Expr.var "vk", Expr.lit (.number mVk),
      Expr.lit (.number 1), Expr.lit (.number payLen)]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sN)], Expr.lit (.number n)]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sK)], Expr.lit (.number k)]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sA)], Expr.lit (.number w)]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sO)], Expr.lit (.number o)]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sL)], Expr.lit (.number l)]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.mload [Expr.lit (.number sB)], Expr.lit (.number b)]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
      [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errVk)])],
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.lit (.number q),
        Expr.builtin Op.calldataload [Expr.lit (.number cPL)]]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.lit (.number n),
        Expr.builtin Op.calldataload [Expr.lit (.number cNI)]]]),
    Stmt.assign ["success"] (Expr.builtin Op.and [Expr.var "success",
      Expr.builtin Op.eq [Expr.builtin Op.calldatasize [],
        Expr.builtin Op.add [Expr.lit (.number cI), Expr.lit (.number (n * 32))]]]),
    Stmt.cond (Expr.builtin Op.iszero [Expr.var "success"])
      [Stmt.exprStmt (Expr.call "fail" [Expr.lit (.number errCd)])] ]

/-- **The rewrite of GEN.0 step 5 (P2).** One hypothesis per name; PROVED. -/
theorem vkBody_eq_vkBodyV (consts : Inline.Consts) (n k w o l b q : Nat)
    {vkLen vkHash errVk mVk payLen sN sK sA sO sL sB cPL cNI cI errCd : Nat}
    (hvk : consts.lookup "vk" = none)
    (hsucc : consts.lookup "success" = none)
    (hVkLen : consts.lookup "EXPECTED_VK_LENGTH" = some vkLen)
    (hVkHash : consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some vkHash)
    (hErrVk : consts.lookup "ERR_VK_MISMATCH" = some errVk)
    (hMVk : consts.lookup "VK_MPTR" = some mVk)
    (hPayLen : consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (hSN : consts.lookup "NUM_INSTANCES_MPTR" = some sN)
    (hSK : consts.lookup "K_MPTR" = some sK)
    (hSA : consts.lookup "HAS_ACCUMULATOR_MPTR" = some sA)
    (hSO : consts.lookup "ACC_OFFSET_MPTR" = some sO)
    (hSL : consts.lookup "NUM_ACC_LIMBS_MPTR" = some sL)
    (hSB : consts.lookup "NUM_ACC_LIMB_BITS_MPTR" = some sB)
    (hCPL : consts.lookup "PROOF_LEN_CPTR" = some cPL)
    (hCNI : consts.lookup "NUM_INSTANCE_CPTR" = some cNI)
    (hCI : consts.lookup "INSTANCE_CPTR" = some cI)
    (hErrCd : consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some errCd) :
    vkBody consts n k w o l b q =
      vkBodyV vkLen vkHash errVk mVk payLen sN sK sA sO sL sB cPL cNI cI errCd n k w o l b q := by
  simp only [vkBody, vkBodyV, vkS1, vkS2, vkS9, vkS10, vkS11, vkS12, vkS13, vkHdr, vkGuard,
    vkVk0, vkSucc0, vkSucc, vkSite_var hvk, vkSite_var hsucc, vkSite_lit hVkLen,
    vkSite_lit hVkHash, vkSite_lit hErrVk, vkSite_lit hMVk, vkSite_lit hPayLen, vkSite_lit hSN,
    vkSite_lit hSK, vkSite_lit hSA, vkSite_lit hSO, vkSite_lit hSL, vkSite_lit hSB,
    vkSite_lit hCPL, vkSite_lit hCNI, vkSite_lit hCI, vkSite_lit hErrCd]

/-! ## 2. The `fail` call summary (the HLP.1 shape, one helper)

  The scope is a variable, so `lookupFun funs "fail"` is stuck under kernel reduction and the
  helper body cannot be inlined. The summary therefore has two parts:

  * the TABLE `Cfail` tests only the callee NAME and the ARITY (both reduce for any `funs`);
  * the TRANSFORMER carries, as its first conjunct, the hypothesis the scope must satisfy -
    `funs` resolves `"fail"` to `failFDecl` (`Blocks/TraceReturn.lean:499`). It cannot be a side
    condition of `CSound`, which quantifies over every `funs`; it becomes one leaf per call site,
    closed from the row's scope hypothesis by `fail_scope_leaf`. -/

/-- The halt record is a revert (`LoweringV2/Shared.lean:54`), in `vk_all`'s existential form. -/
theorem reverted_iff (st : EvmState) :
    Midfall.LoweringV2.Reverted st ↔ ∃ d, st.halted = some (.revert, d) := by
  unfold Midfall.LoweringV2.Reverted Midfall.LoweringV2.revertedOf
  constructor
  · intro h
    split at h
    · rename_i d hd; exact ⟨d, hd⟩
    · cases h
  · rintro ⟨d, hd⟩
    rw [hd]

/-- What a `fail(sel)` call does, for any selector: it halts, and the halt record is a revert.
    First conjunct: the scope obligation. -/
def failT {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g)) :
    (EResult (Bridge.Dialect c g) → Prop) → Prop := fun Q =>
  (∃ cenv, lookupFun funs "fail" = some (failFDecl (c := c) (g := g), cenv)) ∧
  ∀ st2 : EvmState, Midfall.LoweringV2.Reverted st2 → Q (.halt st2)

/-- The call-summary table with the one summary. -/
def Cfail (c : ExternalCalls) (g : ExternalGas) : CT (Bridge.Dialect c g) :=
  fun funs fn args _st =>
    match args with
    | [_] => if fn = "fail" then some (failT funs) else none
    | _ => none

/-- **The summary is a valid contract of the helper body** (`CSound`, `WP.lean:197`). The body
    fact is `tr_fail_body` (`Blocks/TraceReturn.lean:652`), which is what `vk_fail_reverts`
    (`Blocks/VkLoading.lean:449`) reduces to through `vk_fail_expr`: `CSound` speaks about the BODY
    run after the arguments are evaluated, `vk_fail_reverts` about the whole call STATEMENT. -/
theorem Cfail_sound (c : ExternalCalls) (g : ExternalGas) :
    CSound (Bridge.Dialect c g) (Cfail c g) := by
  intro funs fn argvals st1 T hT Q hTQ decl cenv hlook hlen Vend st2 o hbody
  unfold Cfail at hT
  split at hT
  · split at hT
    · cases hT
      obtain ⟨⟨cenv', hl⟩, hQ⟩ := hTQ
      rename_i hfn
      subst hfn
      rw [hl] at hlook
      cases hlook
      cases hbody with
      | block hstmts =>
          obtain ⟨ho, hrev⟩ := tr_fail_body hstmts
          subst ho
          exact ⟨fun h => (by rcases h with h | h <;> cases h), fun _ => hQ _ hrev⟩
    · cases hT
  · cases hT

/-- `wp` with the `fail` summary is sound for every run, any call relation, any gas oracle. -/
theorem allRuns_of_wp_fail {c : ExternalCalls} {g : ExternalGas} (n : Nat)
    {funs : FunEnv (Bridge.Dialect c g)} {V : VEnv (Bridge.Dialect c g)} {st : EvmState}
    {ss : Block EVM.Op} {Q : VEnv (Bridge.Dialect c g) → EvmState → Outcome → Prop}
    (h : wpSS (Bridge.Dialect c g) (Bopen c g) (Cfail c g) n funs V st ss Q) :
    AllRuns funs V st ss Q :=
  wpSS_sound _ (Bopen c g) (Cfail c g) (Bopen_sound c g) (Cfail_sound c g) h

open Lean Elab Tactic Meta in
elab "count_leaves" : tactic => do
  let gs ← getGoals
  logInfo m!"open leaves: {gs.length}"

/-! ## 3. `vk_all_param` -/

/-- A word that is 0 or 1 (the `success` flag). -/
def IsBit (x : U256) : Prop := x = 0 ∨ x = 1

theorem isBit_one : IsBit (1 : U256) := Or.inr rfl

/-- `and(success, eq(..))` keeps the flag a bit. -/
theorem isBit_and_b2w {x : U256} (b : Bool) (hx : IsBit x) : IsBit (x &&& b2w b) := by
  unfold IsBit
  rcases hx with rfl | rfl <;> cases b <;> decide

/-- The skipped `if iszero(success)` guard says the flag is 1. -/
theorem isBit_eq_one {x : U256} (hx : IsBit x) {inst : Decidable (x = 0)}
    (h : b2w (@decide (x = 0) inst) = (0 : U256)) : x = 1 := by
  rcases hx with rfl | rfl
  · simp [b2w] at h
  · rfl

set_option maxRecDepth 10000 in
set_option wpLets false in
set_option profiler true in
set_option profiler.threshold 50 in
/-- **`vk_all` (`VK.lean:26`) FOR EVERY CONSTANT TABLE AND EVERY SCOPE.** Every run of the
    vkLoading block from a clean boundary (`success = 1`) either halts reverted or exits normally
    with `success = 1` and the outer environment restored.

    Scope hypothesis: `hfail` - `funs` resolves `"fail"` to `failFDecl`, the helper
    `vk_fail_reverts` speaks about. No other fact about `funs` is used.

    NO SIDE CONDITION is needed for this postcondition: no bound on any of the fifteen constants.
    (The memory fact of GEN.0 step 6 is not part of this postcondition; its side conditions are
    listed in the memo.) -/
theorem vk_all_param (c : ExternalCalls) (g : ExternalGas)
    (funs funs' : FunEnv (Bridge.Dialect c g))
    (consts : Inline.Consts) (n k w o l b q : Nat)
    (vkLen vkHash errVk mVk payLen sN sK sA sO sL sB cPL cNI cI errCd : Nat)
    (hvk : consts.lookup "vk" = none)
    (hsucc : consts.lookup "success" = none)
    (hVkLen : consts.lookup "EXPECTED_VK_LENGTH" = some vkLen)
    (hVkHash : consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some vkHash)
    (hErrVk : consts.lookup "ERR_VK_MISMATCH" = some errVk)
    (hMVk : consts.lookup "VK_MPTR" = some mVk)
    (hPayLen : consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (hSN : consts.lookup "NUM_INSTANCES_MPTR" = some sN)
    (hSK : consts.lookup "K_MPTR" = some sK)
    (hSA : consts.lookup "HAS_ACCUMULATOR_MPTR" = some sA)
    (hSO : consts.lookup "ACC_OFFSET_MPTR" = some sO)
    (hSL : consts.lookup "NUM_ACC_LIMBS_MPTR" = some sL)
    (hSB : consts.lookup "NUM_ACC_LIMB_BITS_MPTR" = some sB)
    (hCPL : consts.lookup "PROOF_LEN_CPTR" = some cPL)
    (hCNI : consts.lookup "NUM_INSTANCE_CPTR" = some cNI)
    (hCI : consts.lookup "INSTANCE_CPTR" = some cI)
    (hErrCd : consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some errCd)
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (st : EvmState) (rv vk : U256) :
    AllRuns funs [("success", (1 : U256)), ("r", rv), ("vk", vk)] st
      [Stmt.block (vkBody consts n k w o l b q)]
      fun V' st' o => Hold (
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ V' = [("success", (1 : U256)), ("r", rv), ("vk", vk)])) := by
  rw [vkBody_eq_vkBodyV consts n k w o l b q hvk hsucc hVkLen hVkHash hErrVk hMVk hPayLen hSN hSK
    hSA hSO hSL hSB hCPL hCNI hCI hErrCd]
  refine allRuns_of_wp_fail 60 ?_
  wp_run
  count_leaves
  -- leaf 1: the normal exit. `success` is a bit all along; the last skipped guard makes it 1.
  · rename_i h1 h2 h3
    refine ⟨Or.inr ⟨rfl, ?_⟩⟩
    show [("success", _), ("r", rv), ("vk", vk)] = _
    congr 2
    refine isBit_eq_one ?_ h3
    repeat first | exact isBit_one | apply isBit_and_b2w
  -- leaves 2, 4, 6: the scope obligation of the `fail` summary; leaves 3, 5, 7: the revert
  all_goals first
    | exact ⟨_, hfail⟩
    | exact ⟨Or.inl ⟨rfl, ‹Midfall.LoweringV2.Reverted _›⟩⟩
set_option maxRecDepth 10000 in
set_option wpLets false in
set_option profiler true in
set_option profiler.threshold 50 in
/-- **GEN.0 step 6: the memory fact of the normal exit, with NO side condition.** The residue is
    exactly: memory is `copyInto` of the key's code at the WORD value of `VK_MPTR`, source offset 1,
    length the WORD value of `EXPECTED_VK_PAYLOAD_LENGTH`; the environment record is unchanged (so
    `extCodeOf`, calldata are unchanged); the six `mload`s only move `activeWords`. Stated on
    `(BitVec.ofNat 256 mVk).toNat`, i.e. `mVk % 2^256`, it needs no bound; the side conditions
    listed in the memo are what turns it into a statement about `mVk` and `payLen` themselves. -/
theorem vk_all_param_mem (c : ExternalCalls) (g : ExternalGas)
    (funs funs' : FunEnv (Bridge.Dialect c g))
    (consts : Inline.Consts) (n k w o l b q : Nat)
    (vkLen vkHash errVk mVk payLen sN sK sA sO sL sB cPL cNI cI errCd : Nat)
    (hvk : consts.lookup "vk" = none)
    (hsucc : consts.lookup "success" = none)
    (hVkLen : consts.lookup "EXPECTED_VK_LENGTH" = some vkLen)
    (hVkHash : consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some vkHash)
    (hErrVk : consts.lookup "ERR_VK_MISMATCH" = some errVk)
    (hMVk : consts.lookup "VK_MPTR" = some mVk)
    (hPayLen : consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some payLen)
    (hSN : consts.lookup "NUM_INSTANCES_MPTR" = some sN)
    (hSK : consts.lookup "K_MPTR" = some sK)
    (hSA : consts.lookup "HAS_ACCUMULATOR_MPTR" = some sA)
    (hSO : consts.lookup "ACC_OFFSET_MPTR" = some sO)
    (hSL : consts.lookup "NUM_ACC_LIMBS_MPTR" = some sL)
    (hSB : consts.lookup "NUM_ACC_LIMB_BITS_MPTR" = some sB)
    (hCPL : consts.lookup "PROOF_LEN_CPTR" = some cPL)
    (hCNI : consts.lookup "NUM_INSTANCE_CPTR" = some cNI)
    (hCI : consts.lookup "INSTANCE_CPTR" = some cI)
    (hErrCd : consts.lookup "ERR_BAD_CALLDATA_SHAPE" = some errCd)
    (hfail : lookupFun funs "fail" = some (failFDecl, funs'))
    (st : EvmState) (rv vk : U256) :
    AllRuns funs [("success", (1 : U256)), ("r", rv), ("vk", vk)] st
      [Stmt.block (vkBody consts n k w o l b q)]
      fun V' st' o => Hold (
        (o = .halt ∧ Midfall.LoweringV2.Reverted st') ∨
        (o = .normal ∧ V' = [("success", (1 : U256)), ("r", rv), ("vk", vk)] ∧
          st'.memory = copyInto st.memory (BitVec.ofNat 256 mVk).toNat 1
            (BitVec.ofNat 256 payLen).toNat (st.env.extCodeOf vk) ∧
          st'.env = st.env ∧ st'.halted = st.halted)) := by
  rw [vkBody_eq_vkBodyV consts n k w o l b q hvk hsucc hVkLen hVkHash hErrVk hMVk hPayLen hSN hSK
    hSA hSO hSL hSB hCPL hCNI hCI hErrCd]
  refine allRuns_of_wp_fail 60 ?_
  wp_run
  count_leaves
  -- leaf 1: the normal exit. `success` is a bit all along; the last skipped guard makes it 1.
  · rename_i h1 h2 h3
    refine ⟨Or.inr ⟨rfl, ?_, rfl, rfl, rfl⟩⟩
    show [("success", _), ("r", rv), ("vk", vk)] = _
    congr 2
    refine isBit_eq_one ?_ h3
    repeat first | exact isBit_one | apply isBit_and_b2w
  -- leaves 2, 4, 6: the scope obligation of the `fail` summary; leaves 3, 5, 7: the revert
  all_goals first
    | exact ⟨_, hfail⟩
    | exact ⟨Or.inl ⟨rfl, ‹Midfall.LoweringV2.Reverted _›⟩⟩

/-! ## 4. The existence half (GEN.1 step 4) and `wpSS_exists`

  `wpSS_exists` (`WPX.lean:24`) asks `hC : ∀ funs fn args st, C funs fn args st = none`.
  MEASURED (probe `out/probes/PX.lean`): with `Cnone` and a variable scope, `wp_run` on this block
  returns 4 leaves - the normal exit and THREE STUCK leaves `Option.rec … (lookupFun … "fail")`,
  one per `fail` site, each under a hypothesis `guard ≠ 0`. Logically each is closed by refuting its
  guard from the pins, so no summary is needed; but a declaration with a stuck leaf did not
  kernel-check within 60 s whatever closed the leaf (`sorry`, an axiom; with
  `debug.skipKernelTC` the same file takes 12 s). So under a variable scope the existence half
  needs the summary too, i.e. a LIVENESS form of `CSound` and `wpSS_exists` generalised to it. -/
section Live
variable (D : Dialect) [DecidableEq D.Value] (C : CT D)

/-- A summary table is LIVE: when a summary's transformer holds, the callee resolves with the right
    arity and SOME run of its body exists whose result satisfies the continuation. The dual of
    `CSound` (`WP.lean:197`). -/
def CLive : Prop :=
  ∀ funs fn argvals st1 T, C funs fn argvals st1 = some T → ∀ Q, T Q →
    ∃ decl cenv, lookupFun funs fn = some (decl, cenv) ∧ argvals.length = decl.params.length ∧
      ∃ Vend st2 o,
        Step D cenv (decl.params.zip argvals ++ bindZeros D decl.rets) st1
          (.stmt (.block decl.body)) (.sres Vend st2 o) ∧
        (((o = .normal ∨ o = .leave) ∧
            Q (.vals (decl.rets.map fun r => (VEnv.get Vend r).getD D.zero) st2)) ∨
          (o = .halt ∧ Q (.halt st2)))

/-- The table with no summaries is live (so `wpSS_exists_C` below contains `wpSS_exists`). -/
theorem CLive_of_none (hC : ∀ funs fn args st, C funs fn args st = none) : CLive D C := by
  intro funs fn argvals st1 T hT
  rw [hC] at hT
  cases hT

/-- **THE LEMMA THE EXISTENCE HALF NEEDS (statement).** `wpSS_exists` with live summaries instead
    of none. SORRY `wpSS_exists_C`: same induction as `wpSS_exists` (itself a sorry, card T3.2),
    one more case - at a summarised call take the run `CLive` gives. -/
theorem wpSS_exists_C (B : BT D) (hB : BLive D B) (hC : CLive D C)
    {n : Nat} {funs : FunEnv D} {V : VEnv D} {st : D.State} {ss : Block D.Op}
    {Q : VEnv D → D.State → Outcome → Prop} (h : wpSS D B C n funs V st ss Q) :
    ∃ V' st' o, ExecStmts D funs V st ss V' st' o ∧ Q V' st' o := by
  sorry
end Live

/-- The `fail` summary is live: the helper body always has a run (an `mstore`, then a `revert`),
    and by `tr_fail_body` that run halts reverted. PROVED. -/
theorem Cfail_live (c : ExternalCalls) (g : ExternalGas) :
    CLive (Bridge.Dialect c g) (Cfail c g) := by
  intro funs fn argvals st1 T hT Q hTQ
  unfold Cfail at hT
  split at hT
  · split at hT
    · cases hT
      obtain ⟨⟨cenv, hl⟩, hQ⟩ := hTQ
      rename_i hfn
      subst hfn
      refine ⟨failFDecl, cenv, hl, rfl, ?_⟩
      rename_i a
      obtain ⟨v, hshl⟩ : ∃ v, (Bridge.Dialect c g).Builtin Op.shl
          [(Bridge.Dialect c g).litValue (.number 224), a] st1 (.ok [v] st1) :=
        ⟨_, show stepOp Op.shl _ _ = some _ from rfl⟩
      obtain ⟨sm, hmst⟩ : ∃ sm, (Bridge.Dialect c g).Builtin Op.mstore
          [(Bridge.Dialect c g).litValue (.number 0), v] st1 (.ok [] sm) :=
        ⟨_, show stepOp Op.mstore _ _ = some _ from rfl⟩
      obtain ⟨sr, hrvt⟩ : ∃ sr, (Bridge.Dialect c g).Builtin Op.revert
          [(Bridge.Dialect c g).litValue (.number 0), (Bridge.Dialect c g).litValue (.number 4)]
          sm (.halt sr) :=
        ⟨_, show stepOp Op.revert _ _ = some _ from rfl⟩
      have hrun : ∃ V' st' o, ExecStmts (Bridge.Dialect c g)
          (hoist (Bridge.Dialect c g) (failFDecl (c := c) (g := g)).body :: cenv)
          ((failFDecl (c := c) (g := g)).params.zip [a] ++
            bindZeros (Bridge.Dialect c g) (failFDecl (c := c) (g := g)).rets) st1
          (failFDecl (c := c) (g := g)).body V' st' o :=
        ⟨_, sr, .halt, Step.seqCons (D := Bridge.Dialect c g)
          (Step.exprStmt (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil
            (Step.builtinOk (Step.argsCons (Step.argsCons Step.argsNil (Step.var rfl)) Step.lit)
              hshl)) Step.lit) hmst))
          (Step.seqStop (Step.exprStmtHalt (Step.builtinHalt
            (Step.argsCons (Step.argsCons Step.argsNil Step.lit) Step.lit) hrvt)) (by decide))⟩
      obtain ⟨V', st', o, hrun⟩ := hrun
      obtain ⟨ho, hrev⟩ := tr_fail_body hrun
      subst ho
      exact ⟨_, _, _, Step.block hrun, Or.inr ⟨rfl, hQ _ hrev⟩⟩
    · cases hT
  · cases hT

#print axioms vkBody_eq_vkBodyV
#print axioms Cfail_sound
#print axioms vk_all_param
#print axioms vk_all_param_mem
#print axioms Cfail_live
end Midfall.Scratch.ProofTech

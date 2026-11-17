import Midfall.Instances.PoseidonValid
import Midfall.Generator.Vk
import Midfall.Generator.Quotient.QuotientBlocks
import Midfall.Generator.Quotient.VmBuilder
import Midfall.Generator.Quotient.VmRecognizers
import Midfall.Generator.Quotient.VmCertify
import Midfall.Generator.Quotient.FoldCompute
set_option autoImplicit false


namespace Midfall.Lowering.YulParse

open YulSemantics YulSemantics.EVM

abbrev Toks := List String

def isNumTok (t : String) : Bool := !t.isEmpty && t.all Char.isDigit

def isIdentTok (t : String) : Bool :=
  !t.isEmpty && !(t.front.isDigit) &&
    t.all (fun c => c.isAlphanum || c == '_' || c == '$' || c == '.') &&
    !(["let", "if", "for", "switch", "case", "default", "function", "break", "continue", "leave",
      "true", "false"].contains t)

def litOf (t : String) : Option Literal :=
  if t == "true" then some (.bool true)
  else if t == "false" then some (.bool false)
  else if isNumTok t then some (.number t.toNat!)
  else none

/-- comma-separated identifiers up to (not including) a stop token -/
def identList : Nat → Toks → Option (List String × Toks)
  | 0, _ => none
  | fuel + 1, t :: rest =>
      if isIdentTok t then
        match rest with
        | "," :: rest' => (identList fuel rest').map fun (xs, r) => (t :: xs, r)
        | _ => some ([t], rest)
      else none
  | _ + 1, [] => none

mutual
def parseExpr : Nat → Toks → Option (Expr Op × Toks)
  | 0, _ => none
  | fuel + 1, t :: rest =>
      match litOf t with
      | some l => some (.lit l, rest)
      | none =>
          if isIdentTok t then
            match rest with
            | "(" :: ")" :: rest' => some (mkCall t [], rest')
            | "(" :: rest' =>
                (parseArgs fuel rest').map fun (args, r) => (mkCall t args, r)
            | _ => some (.var t, rest)
          else none
  | _ + 1, [] => none

/-- arguments after the opening parenthesis, consuming the closing one -/
def parseArgs : Nat → Toks → Option (List (Expr Op) × Toks)
  | 0, _ => none
  | fuel + 1, toks =>
      match parseExpr fuel toks with
      | some (e, "," :: rest) => (parseArgs fuel rest).map fun (es, r) => (e :: es, r)
      | some (e, ")" :: rest) => some ([e], rest)
      | _ => none
end

mutual
/-- statements up to and including the closing brace of the enclosing block -/
def parseStmts : Nat → Toks → Option (List (Stmt Op) × Toks)
  | 0, _ => none
  | _ + 1, "}" :: rest => some ([], rest)
  | fuel + 1, toks =>
      match parseStmt fuel toks with
      | some (s, rest) => (parseStmts fuel rest).map fun (ss, r) => (s :: ss, r)
      | none => none

def parseBlock : Nat → Toks → Option (List (Stmt Op) × Toks)
  | 0, _ => none
  | fuel + 1, "{" :: rest => parseStmts fuel rest
  | _ + 1, _ => none

def parseCases : Nat → Toks →
    Option (List (Literal × List (Stmt Op)) × Option (List (Stmt Op)) × Toks)
  | 0, _ => none
  | fuel + 1, "case" :: l :: rest =>
      match litOf l, parseBlock fuel rest with
      | some lit, some (body, r) =>
          (parseCases fuel r).map fun (cs, d, r') => ((lit, body) :: cs, d, r')
      | _, _ => none
  | fuel + 1, "default" :: rest =>
      (parseBlock fuel rest).map fun (body, r) => ([], some body, r)
  | _ + 1, toks => some ([], none, toks)

def parseStmt : Nat → Toks → Option (Stmt Op × Toks)
  | 0, _ => none
  | fuel + 1, "{" :: rest => (parseStmts fuel rest).map fun (b, r) => (.block b, r)
  | fuel + 1, "function" :: name :: "(" :: rest =>
      let ps? : Option (List String × Toks) :=
        match rest with
        | ")" :: r => some ([], r)
        | _ => match identList fuel rest with
               | some (ps, ")" :: r) => some (ps, r)
               | _ => none
      match ps? with
      | none => none
      | some (ps, r) =>
          let rs? : Option (List String × Toks) :=
            match r with
            | "-" :: ">" :: r' => identList fuel r'
            | _ => some ([], r)
          match rs? with
          | none => none
          | some (rs, r2) => (parseBlock fuel r2).map fun (b, r3) => (.funDef name ps rs b, r3)
  | fuel + 1, "let" :: rest =>
      match identList fuel rest with
      | some (xs, ":" :: "=" :: r) => (parseExpr fuel r).map fun (e, r') => (.letDecl xs (some e), r')
      | some (xs, r) => some (.letDecl xs none, r)
      | none => none
  | fuel + 1, "if" :: rest =>
      match parseExpr fuel rest with
      | some (c, r) => (parseBlock fuel r).map fun (b, r') => (.cond c b, r')
      | none => none
  | fuel + 1, "switch" :: rest =>
      match parseExpr fuel rest with
      | some (c, r) => (parseCases fuel r).map fun (cs, d, r') => (.switch c cs d, r')
      | none => none
  | fuel + 1, "for" :: rest =>
      match parseBlock fuel rest with
      | some (init, r1) =>
          match parseExpr fuel r1 with
          | some (c, r2) =>
              match parseBlock fuel r2 with
              | some (post, r3) =>
                  (parseBlock fuel r3).map fun (body, r4) => (.forLoop init c post body, r4)
              | none => none
          | none => none
      | none => none
  | _ + 1, "break" :: rest => some (.break, rest)
  | _ + 1, "continue" :: rest => some (.continue, rest)
  | _ + 1, "leave" :: rest => some (.leave, rest)
  | fuel + 1, toks =>
      -- assignment `a, b := e` or an expression statement
      match identList fuel toks with
      | some (xs, ":" :: "=" :: r) => (parseExpr fuel r).map fun (e, r') => (.assign xs e, r')
      | _ => (parseExpr fuel toks).map fun (e, r) => (.exprStmt e, r)
end

/-- A whole block given as a token stream WITH its braces. All tokens must be consumed. -/
def parseTokens (toks : Toks) : Option (Block Op) :=
  match parseBlock (toks.length + 1) toks with
  | some (b, []) => some b
  | _ => none

/-- Generated lines (no enclosing braces). -/
def parseLines (ls : List String) : Option (Block Op) :=
  parseTokens ("{" :: Midfall.Generator.yulTokens (String.intercalate "\n" ls) ++ ["}"])

end Midfall.Lowering.YulParse

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-- Byte address of a layout pointer (same adapter as `Inv.ptrAddr`). -/
def cAddr (q : Ptr) : Nat := Value.asUsizeNat q.value

/-- THE CONTRACT CONSTANT TABLE AS DATA, in the order of `templates/partials/verifier/Constants.sol`.
    Every address is read from the PLAN VIEW (the record `Inv` reads), every length from the plan
    view's payload, every calldata pointer from the plan view's proof layout. Only the build-time
    numbers that the plan view does not carry come from the model: the three optional-arm selectors
    (`expectedVkCodehash`, `quotientExternal`/`expectedQuotient*`, `expectedHasAccumulator`), the
    gas schedule and the two derived gas numbers. The 14 trailing entries are template literals. -/
def expectedConsts (pv : PlanView) (m : Model) : List (String × Nat) :=
  let M := pv.memory
  let H := m.vkHeader
  let hdr (w : Nat) : Nat := cAddr (Ptr.add M.vkMptr w)
  (match m.expectedVkCodehash with
    | some _ =>
        [ ("EXPECTED_VK_PAYLOAD_LENGTH", pv.vk.len)
        , ("EXPECTED_VK_LENGTH", pv.vk.len + 1)
        , ("EXPECTED_VK_CODEHASH_WORD", (keccak256 pv.vk.runtimeBytes).toNat) ]
    | none => []) ++
  (match m.quotientExternal, m.expectedQuotientCodehash with
    | some _, some h =>
        [ ("EXPECTED_QUOTIENT_LENGTH", m.expectedQuotientLen.getD 0)
        , ("EXPECTED_QUOTIENT_CODEHASH_WORD", h.toNat) ]
    | _, _ => []) ++
  [ ("PROOF_LEN_CPTR", pv.proofLayout.proofCptr - 32)
  , ("PROOF_CPTR", pv.proofLayout.proofCptr)
  , ("NUM_INSTANCE_CPTR", pv.proofLayout.proofEnd)
  , ("INSTANCE_CPTR", pv.proofLayout.proofEnd + 32)
  , ("TRANSCRIPT_MPTR", M.transcriptMptr)
  , ("RETURN_MPTR", M.verifierReturnMptr)
  , ("VK_MPTR", cAddr M.vkMptr)
  , ("VK_DIGEST_MPTR", hdr H.vkDigest)
  , ("NUM_INSTANCES_MPTR", hdr H.numInstances)
  , ("K_MPTR", hdr H.k)
  , ("N_INV_MPTR", hdr H.nInv)
  , ("OMEGA_MPTR", hdr H.omega)
  , ("OMEGA_INV_MPTR", hdr H.omegaInv)
  , ("OMEGA_INV_TO_L_MPTR", hdr H.omegaInvToL)
  , ("HAS_ACCUMULATOR_MPTR", hdr H.hasAccumulator)
  , ("ACC_OFFSET_MPTR", hdr H.accOffset)
  , ("NUM_ACC_LIMBS_MPTR", hdr H.numAccLimbs)
  , ("NUM_ACC_LIMB_BITS_MPTR", hdr H.numAccLimbBits)
  , ("G1_BASE_MPTR", hdr H.g1Base)
  , ("G2_BASE_MPTR", hdr H.g2Base)
  , ("NEG_S_G2_BASE_MPTR", hdr H.negSG2Base)
  , ("CHALLENGE_MPTR", cAddr M.challengeMptr)
  , ("THETA_MPTR", cAddr M.thetaMptr)
  , ("BETA_MPTR", cAddr M.betaMptr)
  , ("GAMMA_MPTR", cAddr M.gammaMptr)
  , ("TRASH_CHALLENGE_MPTR", cAddr M.trashChallengeMptr)
  , ("Y_MPTR", cAddr M.yMptr)
  , ("X_MPTR", cAddr M.xMptr)
  , ("X1_MPTR", cAddr M.x1Mptr)
  , ("X2_MPTR", cAddr M.x2Mptr)
  , ("X3_MPTR", cAddr M.x3Mptr)
  , ("X4_MPTR", cAddr M.x4Mptr)
  , ("F_COM_MPTR", cAddr M.fComMptr)
  , ("PI_MPTR", cAddr M.piMptr)
  , ("ACC_LHS_MPTR", cAddr M.accLhsMptr)
  , ("ACC_RHS_MPTR", cAddr M.accRhsMptr)
  , ("X_N_MPTR", cAddr M.xNMptr)
  , ("X_N_MINUS_1_INV_MPTR", cAddr M.xNMinus1InvMptr)
  , ("L_LAST_MPTR", cAddr M.lLastMptr)
  , ("L_BLIND_MPTR", cAddr M.lBlindMptr)
  , ("L_0_MPTR", cAddr M.l0Mptr)
  , ("INSTANCE_EVAL_MPTR", cAddr M.instanceEvalMptr)
  , ("QUOTIENT_EVAL_MPTR", cAddr M.quotientEvalMptr)
  , ("QUOTIENT_MPTR", cAddr M.quotientMptr)
  , ("F_EVAL_MPTR", cAddr M.fEvalMptr)
  , ("V_MPTR", cAddr M.vMptr)
  , ("FINAL_COM_MPTR", cAddr M.finalComMptr)
  , ("PAIRING_LHS_MPTR", cAddr M.pairingLhsMptr)
  , ("PAIRING_RHS_MPTR", cAddr M.pairingRhsMptr)
  , ("ROT_POINTS_MPTR", cAddr M.rotPointsMptr)
  , ("X1_POWERS_MPTR", cAddr M.x1PowersMptr)
  , ("Q_COM_MPTR", cAddr M.qComMptr)
  , ("Q_EVAL_SET_MPTR", cAddr M.qEvalSetMptr)
  , ("Q_EVAL_CPTR_MPTR", cAddr M.qEvalCptrMptr)
  , ("G1_IDENTITY_MPTR", cAddr M.g1IdentityMptr)
  , ("REVERSED_EVALS_MPTR", cAddr M.reversedEvalsMptr)
  , ("SELECTOR_ACC_MPTR", M.selectorAccMptr)
  , ("QUOTIENT_RETURN_MPTR", M.quotientReturnMptr)
  , ("BATCH_INV_SCRATCH_MPTR", M.batchInvertScratchMptr)
  , ("LAGRANGE_DENOMS_MPTR", M.lagrangeDenomsMptr)
  , ("TRACE_U256_MPTR", M.traceU256Mptr)
  , ("ADVICE_COMMS_MPTR_BASE", cAddr M.adviceCommsMptrBase)
  , ("LOOKUP_M_COMMS_MPTR_BASE", cAddr M.lookupMCommsMptrBase)
  , ("PERM_Z_COMMS_MPTR_BASE", cAddr M.permZCommsMptrBase)
  , ("LOOKUP_HELPER_COMMS_MPTR_BASE", cAddr M.lookupHelperCommsMptrBase)
  , ("LOOKUP_Z_COMMS_MPTR_BASE", cAddr M.lookupZCommsMptrBase)
  , ("TRASHCAN_COMMS_MPTR_BASE", cAddr M.trashcanCommsMptrBase)
  , ("QUOTIENT_LIMB_COMMS_MPTR_BASE", cAddr M.quotientLimbCommsMptrBase)
  , ("G1ADD_GAS", m.templateConstants.gas.g1add)
  , ("G1MSM_GAS_1PAIR", m.templateConstants.gas.g1msmOnePair)
  , ("PAIRING_GAS_2PAIR", m.templateConstants.gas.pairingTwoPair)
  , ("MODEXP_GAS", m.templateConstants.gas.modexp)
  , ("G1MSM_GAS_SMOKE", m.constructorG1msmSmokeGas) ] ++
  (if m.expectedHasAccumulator then [("ACC_RHS_MSM_GAS", m.accRhsMsmGas)] else []) ++
  [ ("ERR_BAD_CALLDATA_SHAPE", 0x1b99e37c)
  , ("ERR_VK_MISMATCH", 0xa447d73e)
  , ("ERR_NON_CANONICAL_SCALAR", 0x77530042)
  , ("ERR_BAD_POINT_ENCODING", 0xf27905ec)
  , ("ERR_PRECOMPILE_FAILED", 0x84e81692)
  , ("ERR_PROOF_REJECTED", 0xc3b0d8cd)
  , ("ERR_QUOTIENT_PROGRAM_INVALID", 0x3cc81b89)
  , ("ERR_MEMORY_LAYOUT_VIOLATED", 0xc9888d23)
  , ("FR_MODULUS", 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
  , ("BLS_P_HI", 0x1a0111ea397fe69a4b1ba7b6434bacd7)
  , ("BLS_P_MINUS_ONE_LO", 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_1", 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84) ]

/-- The names the un-inlined program reads that it does not bind: exactly the contract constants
    plus the two wrapper locals. Includes the ABI guard block, which `mainClosed` omits. -/
def progConstNames (pv : PlanView) (m : Model) : List String :=
  (freeNames (abiGuardBlock m ++ mainAsmRaw pv)).filter
    fun x => x != "vk" && x != "quotientEvaluator"

/-- Every constant line of the rendered `Constants.sol` that declares a `uint256 internal constant`
    has a LITERAL right-hand side (decimal or 0x-hex digits only) - the KAT `Program.lean:55-57`
    asks for and never got. Without it `solConstantLine?` silently mis-parses `sub(0, 0x20)`. -/
def constLinesLiteral (m : Model) : Bool :=
  ((renderConstants (partialCtxOfVerifier m)).splitOn "\n").all fun l =>
    match l.splitOn "uint256 internal constant " with
    | [_, rest] =>
        (match rest.splitOn "=" with
         | [_, rhs] =>
             let v := ((rhs.splitOn ";").headD "").trimAscii.toString
             let digits := if v.startsWith "0x" then (v.drop 2).toString else v
             !digits.isEmpty && digits.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
         | _ => false)
    | _ => true

/-- **THE ONE CONSTANTS-COHERENCE CLAUSE.** Four conjuncts, all computations on the render:
    1. first-headline scope: no Direct lowering (its constant lines are free strings);
    2. every constant line parses as a literal;
    3. the table read back from the rendered text IS the data-level table of the plan view;
    4. no name is declared twice, and every name the program reads is declared. -/
def constsCoherent (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone &&
  constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  ((expectedConsts pv m).map Prod.fst).Nodup &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x

def ConstsCoherent (pv : PlanView) (m : Model) : Prop := constsCoherent pv m = true

/-- What a block proof uses: a table lookup is a lookup in the DATA table. Generic in the render. -/
theorem consts_lookup_of_coherent {pv : PlanView} {m : Model} (h : ConstsCoherent pv m)
    (name : String) :
    (constTableOf m).lookup name = (expectedConsts pv m).lookup name := by
  have h3 : (constTableOf m == expectedConsts pv m) = true := by
    unfold ConstsCoherent constsCoherent at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.2
  rw [eq_of_beq h3]

end Midfall.LoweringV2

/-!
  PLAN-V3 / area OBJECT: the proposed statements, typechecked against the tree at 6bde89f.
  Sections:
   1. `Except.getOk` (closes DECISIONS-PENDING section 9 with no v1 edit and no frozen change)
   2. `Generator/PlanNew.lean` (proposed): the ported `LoweringPlan::new`, generic
   3. `LoweringV2/Generated.lean` (proposed): `GenOut`, `generateAll`, `Render.GeneratedBy`
   4. program well-scopedness checks (`callsResolved`, `noShadow`)
   5. key coherence: `PayloadAgrees`
   6. `Render.ValidV3`
   7. evaluation at the fixture, on the DERIVED render
-/

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering
open Midfall.Generator.QuotientFold Midfall.Generator.QuotientFoldCompute
open Midfall.Generator.QuotientBuilder Midfall.Generator.QuotientBlocks
open Midfall.Generator.QuotientEvaluator Midfall.Generator.QuotientRecognizers
open YulSemantics YulSemantics.EVM

/-! ## 1. The total projection of an `Except` along a Bool proof -/

/-- The `.ok` value of an `Except` whose `isOk` is `true`. The motive is NON-dependent in the
    scrutinee (the proof argument is about a Bool), which is what `poseidonModelVal`'s
    `match h : poseidonModel with` lacks. -/
def Except.getOk {ε α : Type} : (e : Except ε α) → e.isOk = true → α
  | .ok a, _ => a
  | .error _, h => by simp [Except.isOk, Except.toBool] at h

theorem Except.eq_ok_getOk {ε α : Type} (e : Except ε α) (h : e.isOk = true) :
    e = .ok (e.getOk h) := by
  cases e with
  | ok a => rfl
  | error _ => simp [Except.isOk, Except.toBool] at h

namespace Midfall.Generator.PlanNew

/-! ## 2. `LoweringPlan::new` (plan.rs:235-329), generic in the scalar field -/

def pn (q : Ptr) : Nat := Value.asUsizeNat q.value

/-- R9 field dictionary of `Fr p` with the permutation DELTA supplied by the caller. -/
def frFieldCtx {p : ℕ} [Fact (Nat.Prime p)] (delta : Fr p) : FieldCtx (Fr p) :=
  { zero := 0, one := 1, add := fun a b => a + b, mul := fun a b => a * b, neg := fun a => -a
    eqF := fun a b => decide (a = b), isZero := fun a => decide (a = 0), powNat := fun b e => b ^ e
    repr := fun v => bytesToNats (frToRepr v), delta := delta }

variable {F : Type} [BEq F]

/-- rust: QRS:425-527 `quotient_program_plan`. (`validate_execution_manifest`, QVM:442-470, is
    the one callee still to port; it only panics.) -/
def quotientProgramPlan (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (dat : Data) : Except Fault QuotientProgramPlan := do
  let parts ← quotientIdentityParts field cs meta_ dat
  let all := parts.allIdentities
  let selectorFold ← liftQVM (selectorFoldPlan all parts.sortedSimple.length)
  let inlineCount := min parts.gates.length defaultHybridQuotientInlineIdentities
  let remaining := parts.gates.drop inlineCount
  let nativeIdx ← liftQVM (nativeGateIndices remaining)
  let nativePermutation := meta_.numPermutationZs > 0
  let nativeLookup := meta_.numLookups > 0
  let structuredTrashTail := meta_.numTrashcans > 0
  let selected := remaining.zipIdx.filter (fun q => nativeIdx.contains q.2)
  let nativeIndexByGate : List (Nat × Nat) := selected.zipIdx.map (fun q => (q.1.2, q.2))
  let gateItems := remaining.zipIdx.map fun q =>
    match nativeIndexByGate.lookup q.2 with
    | some n => QuotientProgramItem.nativeIdentity n
    | none => QuotientProgramItem.identity q.1
  let permItems := if nativePermutation then [QuotientProgramItem.nativePermutation]
    else parts.permutation.map QuotientProgramItem.identity
  let lookupItems := if nativeLookup then [QuotientProgramItem.nativeLookup]
    else parts.lookup.map QuotientProgramItem.identity
  let trashItems := if structuredTrashTail then [] else parts.trash.map QuotientProgramItem.identity
  pure { inlineIdentities := parts.gates.take inlineCount
         items := gateItems ++ permItems ++ lookupItems ++ trashItems
         nativeIdentities := selected.map (fun q => q.1)
         nativePermutationIdentities := if nativePermutation then parts.permutation else []
         nativeLookupIdentities := if nativeLookup then parts.lookup else []
         structuredTailIdentities := if structuredTrashTail then parts.trash else []
         sortedSimple := parts.sortedSimple
         hasNativePermutation := nativePermutation
         hasNativeLookup := nativeLookup
         selectorFold := selectorFold }

/-- rust: QRS:2120-2146 `build_quotient_program_items_with_limb_ops`. -/
def buildQuotientProgramItemsWithLimbOps (items : List QuotientProgramItem)
    (selectorFold : SelectorFoldPlan) (limb : Bool) : Except Fault QuotientProgramBuild :=
  liftQVM do
    let s ← items.foldlM (fun s item =>
      match item with
      | QuotientProgramItem.identity identity =>
          identityExpr shapeRecognizers s identity.expr identity.target
            (selectorFold.gapFor identity)
      | QuotientProgramItem.nativePermutation => nativePermutation s
      | QuotientProgramItem.nativeLookup => nativeLookup s
      | QuotientProgramItem.nativeIdentity n => nativeIdentity s n) (withLimbVmOps limb)
    finish s

/-- rust: QRS:1402-1465 `native_callback_scratch_words`. -/
def nativeCallbackScratchWords (field : FieldCtx F) (cs : ConstraintSystem F)
    (meta_ : ConstraintSystemMeta) (dat : Data) (plan : QuotientProgramPlan) :
    Except Fault Nat := do
  let permWords :=
    if plan.hasNativePermutation && meta_.numPermutationZs != 0 then
      2 * meta_.permutationColumns.length + 2 * meta_.numPermutationZs
        + (meta_.numPermutationZs - 1) + 1
    else 0
  let (maxPar, _) ← (structuredLookupMaxParallel (F := F) meta_).run
    (Evaluator.new field cs meta_ dat)
  pure (max permWords (if plan.hasNativeLookup then maxPar * 3 else 0))

def usedHas (bs : Bytes) (op : Nat) : Bool := (bytesToNats bs).contains op

/-- rust: QRS:259-294 `quotient_opcode_usage`. -/
def quotientOpcodeUsage (u : Bytes) : QuotientVmOpcodeUsage :=
  { pushConst := usedHas u qOpPushConst, pushMemLiteral := usedHas u qOpPushMemLiteral
    pushMemToken := usedHas u qOpPushMemToken, pushMemTokenOffset := usedHas u qOpPushMemTokenOffset
    pushMemU16 := usedHas u qOpPushMemU16, add := usedHas u qOpAdd, mul := usedHas u qOpMul
    neg := usedHas u qOpNeg, pushConstU8 := usedHas u qOpPushConstU8
    foldMain := usedHas u qOpFoldMain, foldSelector := usedHas u qOpFoldSelector
    addConstU8 := usedHas u qOpAddConstU8, mulConstU8 := usedHas u qOpMulConstU8
    addConst := usedHas u qOpAddConst, mulConst := usedHas u qOpMulConst
    addMemU16 := usedHas u qOpAddMemU16, mulMemU16 := usedHas u qOpMulMemU16
    addMulMemMemConstU8 := usedHas u qOpAddMulMemMemConstU8
    addMulConstU8MemU16 := usedHas u qOpAddMulConstU8MemU16
    addMulMemMem := usedHas u qOpAddMulMemMem
    runAddMulMemMemConstU8 := usedHas u qOpRunAddMulMemMemConstU8
    runAddMulConstU8MemU16 := usedHas u qOpRunAddMulConstU8MemU16
    affineSum := usedHas u qOpAffineSum, nativePermutation := usedHas u qOpNativePermutation
    nativeLookup := usedHas u qOpNativeLookup, nativeIdentity := usedHas u qOpNativeIdentity
    lin7 := usedHas u qOpLin7, bilin7Row := usedHas u qOpBilin7Row
    bilin7Pairwise := usedHas u qOpBilin7Pairwise, modarith7 := usedHas u qOpModarith7
    pow5 := usedHas u qOpPow5 }

/-- rust: QRS:297-311 `quotient_mem_usage`. -/
def quotientMemUsage (u : Bytes) : QuotientVmMemUsage :=
  { l0 := usedHas u qMemL0, lLast := usedHas u qMemLLast, lBlind := usedHas u qMemLBlind
    beta := usedHas u qMemBeta, gamma := usedHas u qMemGamma, x := usedHas u qMemX
    theta := usedHas u qMemTheta, trashChallenge := usedHas u qMemTrashChallenge
    instanceEval := usedHas u qMemInstanceEval }

/-- rust: QRS:189-238 `quotient_template_program`. -/
def quotientTemplateProgram (build : QuotientProgramBuild) (vk : Halo2VerifyingKey)
    (vkMptr : Ptr) (memory : VerifierMemoryLayout) (selectorFold : SelectorFoldPlan)
    (opModel : QuotientValidator.QuotientOperandModel) :
    Except Fault (QuotientProgram × Nat × QuotientStateSlots) := do
  let chunks := PackedProgramCodec.encodeWords build.bytes
  let constOff ← match vk.quotientConstOffsetWords with
    | some o => pure o
    | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/quotient.rs:204")
  let progOff ← match vk.quotientProgramOffsetWords with
    | some o => pure o
    | none => throw (Fault.panic "proofs/solidity-verifier/src/lowering/quotient.rs:206")
  unless build.consts.length ≤ vk.quotientConstWords do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/quotient.rs:207")
  unless chunks.length ≤ vk.quotientProgramWords do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/quotient.rs:211")
  let stateSlots := QuotientStateSlots.new memory.quotientTmpMptr
  let guards ← quotientVmGuards opModel memory
  pure ({ len := build.bytes.size, opUsage := quotientOpcodeUsage build.usedOps
          memUsage := quotientMemUsage build.usedMemTokens
          constMptr := pn (vkMptr.add constOff)
          evalNumerMptr := stateSlots.evalNumerMptr, traceIdMptr := stateSlots.traceIdMptr
          selectorPowerMptr := stateSlots.selectorPowerMptr
          selectorMaxPower := selectorFold.maxPower
          selectorTailUpdates := selectorTailUpdates selectorFold
          stackMptr := memory.quotientStackMptr, programMptr := pn (vkMptr.add progOff)
          guards := guards },
        memory.quotientStackMptr, stateSlots)

/-- The payload's two quotient sections ARE the build (vk.rs:443-448 writes them, :456-463
    re-checks them). Needed because the payload is an INPUT here, not the output of
    `generate_vk`. -/
def vkCarriesBuild (vk : Halo2VerifyingKey) (build : QuotientProgramBuild) : Bool :=
  match vk.quotientConstOffsetWords, vk.quotientProgramOffsetWords with
  | some qc, some qp =>
      let words := vk.constants.map (·.2)
      let prog := PackedProgramCodec.encodeWords build.bytes
      (words.drop qc).take vk.quotientConstWords ==
          build.consts ++ List.replicate (vk.quotientConstWords - build.consts.length) 0 &&
        (words.drop qp).take vk.quotientProgramWords ==
          prog ++ List.replicate (vk.quotientProgramWords - prog.length) 0
  | _, _ => false

/-- **`LoweringPlan::new`** (plan.rs:235-329) for a GIVEN VK payload: the stable static layout,
    the proof layout from the post-processed meta, the quotient plan and build, the memory
    layout, the template program, then the generator's own invariant validation and the
    dual-build certification - each of the last two a panic in the reference. -/
def newFromVk {p : ℕ} {G₁ : Type} (feat : Features) (field : FieldCtx F)
    (cs : ConstraintSystem F) (inputs : VerifierBuildInputs p G₁ Unit)
    (vk : Halo2VerifyingKey) : Except Fault (LoweringPlan Unit Unit) := do
  let env : VkBuildEnv Unit :=
    { newVerifierMemoryLayout := VerifierMemoryLayout.new
      compactQuotientProgramFor := fun _ _ => .error (Fault.panic "unused")
      quotientProgramPlan := fun _ _ => .error (Fault.panic "unused")
      buildQuotientProgramItems := fun _ => .error (Fault.panic "unused") }
  let (vkMptr, meta_, dat, _) ← metaDataForStableStaticLayout feat env inputs vk
  let proofLayout ← ProofCalldataLayout.fromProtocol meta_.protocol abiVerifyProofProofCptr
    meta_.numEvals meta_.numPointSets
  let qplan ← quotientProgramPlan field cs meta_ dat
  let build ← buildQuotientProgramItemsWithLimbOps qplan.items qplan.selectorFold
    defaultQuotientLimbVmOps
  let nativeWords ← nativeCallbackScratchWords field cs meta_ dat qplan
  let pcsReq ← memoryRequirements meta_ dat
  let accTerms ← accMsmTerms inputs.accEncoding inputs.numInstances
  let memory ← memoryLayoutFor env inputs meta_ vk vkMptr
    { verifierMemoryLayoutConfigDefault with
      quotientStateWords := quotientStateWords qplan.selectorFold,
      quotientStackWords := max build.maxStack nativeWords,
      accMsmTerms := accTerms, pcs := pcsReq }
  let opModel ← quotientOperandModel meta_ dat vk vkMptr memory build qplan.selectorFold
  let (program, stackMptr, stateSlots) ←
    quotientTemplateProgram build vk vkMptr memory qplan.selectorFold opModel
  let plan : LoweringPlan Unit Unit :=
    LoweringPlan.mk vk vkMptr meta_ dat proofLayout QuotientLowering.vm qplan.sortedSimple
      (some { plan := qplan, build := build, program := program, stackMptr := stackMptr,
              stateSlots := stateSlots }) none pcsReq memory
  -- plan.rs:307-308
  match ← plan.validateGeneratorInvariants with
  | .error _ => throw (Fault.panic "proofs/solidity-verifier/src/lowering/plan.rs:308")
  | .ok () => pure ()
  -- plan.rs:313-325
  let baseline ← buildQuotientProgramItemsWithLimbOps qplan.items qplan.selectorFold false
  match QuotientCertify.certifyQuotientBuildsAgree qplan build baseline vk with
  | .error _ => throw (Fault.panic "proofs/solidity-verifier/src/lowering/plan.rs:325")
  | .ok () => pure ()
  unless vkCarriesBuild vk build do
    throw (Fault.panic "proofs/solidity-verifier/src/lowering/vk.rs:457")
  pure plan

/-- rust: plan.rs:381-394 `compact_quotient_blocks`. -/
def compactBlocksOf (field : FieldCtx F) (cs : ConstraintSystem F) (L : LoweringPlan Unit Unit)
    (trace : Bool) : Except Fault QuotientComputationBlocks := do
  let q ← L.vmQuotient
  let (blocks, _) ← compactQuotientComputationBlocks field cs L.meta_ L.data q.plan
    q.stackMptr q.stateSlots trace
  pure blocks

end Midfall.Generator.PlanNew

namespace Midfall.LoweringV2

open Midfall.Generator.PlanNew Midfall.Assumptions

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 3. The generator, end to end, and the ONE generated-by clause -/

/-- What the generator produces for one render. -/
structure GenOut where
  plan : LoweringPlan Unit Unit
  qblocks : QuotientComputationBlocks
  model : Model

/-- THE GENERATOR: constraint system, configuration and VK payload in; plan, compact quotient
    blocks and render model out. `generate_verifier_from_plan` panics unless `validate_layout`
    passes (artifacts.rs:337-339), so that check is part of it. -/
def generateAll (feat : Features) (delta : Fr p) (vk : VerifyingKey (Fr p) G₁)
    (cfg : GeneratorConfig) (payload : Halo2VerifyingKey) (inputs : ArtifactBuildInputs)
    (flags : RenderFlags) : Except Fault GenOut := do
  let field := frFieldCtx delta
  let m0 ← ConstraintSystemMeta.new feat vk.cs cfg.numCommittedInstances
  let bi : VerifierBuildInputs p G₁ Unit :=
    { params := { gLagrange := [], g2 := (), sG2 := () }
      vk := vk, numInstances := cfg.numInstances
      numCommittedInstances := cfg.numCommittedInstances
      accEncoding := cfg.accumulator, meta_ := m0 }
  let plan ← newFromVk feat field vk.cs bi payload
  let blocks ← compactBlocksOf field vk.cs plan flags.trace
  let model ← generateVerifierFromPlan (fun _ _ => blocks) inputs flags plan
  match Halo2Verifier.validateLayout model with
  | .error _ => throw (Fault.panic "proofs/solidity-verifier/src/lowering/artifacts.rs:338")
  | .ok () => pure ()
  pure { plan := plan, qblocks := blocks, model := model }

namespace Render

variable (R : Render p G₁ G₂ Gₜ)

/-- The generator run on THIS render's verifier-side inputs. The permutation DELTA the quotient
    blocks print is the Lean verifier's own `E.delta`. -/
def generated : Except Fault GenOut :=
  generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags

/-- **THE GENERATED-BY CLAUSE.** Replaces frozen clauses 1 `circuitMeta`, 2 `layout`,
    3 `invariants`, 4 `model`, the `validate_layout` gap (B-7), the VM-lowering gap (B+3),
    `vkPins.numInst`, and makes `E.delta` reach the program text (H-7). -/
def GeneratedBy : Prop :=
  ∃ out, R.generated = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧
    out.model = R.model

end Render

/-! ## 4. Program well-scopedness (decidable; closes B-4 and B-5) -/

mutual
def callSitesE : Expr EVM.Op → List (String × Nat)
  | Expr.call f args => (f, args.length) :: callSitesEs args
  | Expr.builtin _ args => callSitesEs args
  | _ => []
def callSitesEs : List (Expr EVM.Op) → List (String × Nat)
  | [] => []
  | e :: es => callSitesE e ++ callSitesEs es
end

mutual
def callSitesS : Stmt EVM.Op → List (String × Nat)
  | Stmt.block body => callSitesSs body
  | Stmt.funDef _ _ _ body => callSitesSs body
  | Stmt.letDecl _ (some e) => callSitesE e
  | Stmt.assign _ e => callSitesE e
  | Stmt.cond c body => callSitesE c ++ callSitesSs body
  | Stmt.switch c cases dflt =>
      callSitesE c ++ callSitesSC cases ++
        (match dflt with | some d => callSitesSs d | none => [])
  | Stmt.forLoop init c post body =>
      callSitesSs init ++ callSitesE c ++ callSitesSs post ++ callSitesSs body
  | Stmt.exprStmt e => callSitesE e
  | _ => []
termination_by s => sizeOf s
def callSitesSs : List (Stmt EVM.Op) → List (String × Nat)
  | [] => []
  | s :: ss => callSitesS s ++ callSitesSs ss
termination_by ss => sizeOf ss
def callSitesSC : List (Literal × List (Stmt EVM.Op)) → List (String × Nat)
  | [] => []
  | (_, body) :: rest => callSitesSs body ++ callSitesSC rest
termination_by cs => sizeOf cs
end

/-- The functions a block defines at its top level, with their arities. -/
def funSigsOf (blk : YulBlock) : List (String × Nat) :=
  blk.filterMap fun s => match s with | .funDef n ps _ _ => some (n, ps.length) | _ => none

/-- Every user call resolves to a top-level definition of the main block with the same arity;
    no definition is named after a built-in; no name is defined twice. With it, a `.call` node
    can never be a mis-spelled built-in and no run is stuck on an unresolved callee. -/
def callsResolved (main : YulBlock) : Bool :=
  let sigs := funSigsOf main
  (callSitesSs main).all (fun c => sigs.contains c) &&
    sigs.all (fun s => (EVM.parse s.1).isNone) &&
    decide ((sigs.map Prod.fst).Nodup)

/-- No binder of the program is the name of a contract constant (solc rejects it too). This is
    the hypothesis `inline_append` needs and no clause supplied (B-5). -/
def noShadow (consts : List (String × Nat)) (prog : YulBlock) : Bool :=
  (boundSs prog).all fun x => !(consts.map Prod.fst).contains x

/-! ## 5. Key coherence: what the payload must say about the Lean verifier's key -/

def g1WordsBytes (w : G1Words) : Bytes :=
  (wordToBytesBE w.xHi).append ((wordToBytesBE w.xLo).append
    ((wordToBytesBE w.yHi).append (wordToBytesBE w.yLo)))

def payloadWord (vk : Halo2VerifyingKey) (i : Nat) : Word256 := (vk.constants.getD i ("", 0)).2

/-- Every header word and every commitment word of the payload is the encoding of the
    corresponding datum of the Lean verifier's key. Replaces `EnvAgrees.vkDigestWord` (one word)
    and v1's `VkSlotsAgree`; the G2 half is stated through `encG2` as v1 did. -/
structure PayloadAgrees (R : Render p G₁ G₂ Gₜ) : Prop where
  digest : payloadWord R.plan.vk 0 = frWord R.vk.transcriptRepr
  numInstances : (payloadWord R.plan.vk 1).toNat = R.cfg.numInstances
  k : (payloadWord R.plan.vk 2).toNat = R.vk.domain.k
  nInv : payloadWord R.plan.vk 3 = frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)
  omega : payloadWord R.plan.vk 4 = frWord R.vk.domain.omega
  omegaInv : payloadWord R.plan.vk 5 = frWord R.vk.domain.omegaInv
  omegaInvToL : payloadWord R.plan.vk 6 =
    frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs)
  accWords : ((payloadWord R.plan.vk 7).toNat, (payloadWord R.plan.vk 8).toNat,
      (payloadWord R.plan.vk 9).toNat, (payloadWord R.plan.vk 10).toNat) =
    accWordsOfEncoding R.cfg.accumulator
  g1Base : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip (AdmissiblePairing.g₁ (G₂ := G₂) (Gₜ := Gₜ))
  g2Base : vkG2Words R.pv vkG2BaseSlot = R.encG2 (AdmissiblePairing.g₂ (G₁ := G₁) (Gₜ := Gₜ))
  negSG2 : vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 R.sG2gen⁻¹
  fixed : R.plan.vk.fixedComms.map g1WordsBytes = R.vk.fixedCommitments.toList.map R.E.g1.toEip
  perm : R.plan.vk.permutationComms.map g1WordsBytes =
    R.vk.permutation.commitments.toList.map R.E.g1.toEip

end Midfall.LoweringV2


/-! ## 6. The repaired validity predicate -/

namespace Midfall.LoweringV2

open Midfall.Lowering.YulParse Midfall.Assumptions Midfall.Yul Midfall.Yul.Bridge

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-- The parse of the two assembly texts the ported generator prints. -/
def parsedMain? (m : Model) : Option YulBlock := parseTokens (mainAssemblyTokens m)
def parsedGuard? (m : Model) : Option YulBlock := parseTokens (abiGuardTokens m)

/-- STRUCTURAL codegen agreement: the emitted AST IS the parse of the text (`stmtsBeq`), with
    built-in versus user call resolved by the vendored `EVM.mkCall`. Strictly stronger than the
    frozen token equality (`codegenAgrees`), which cannot tell `.builtin` from `.call`. -/
def codegenStruct (main : YulBlock) (m : Model) : Bool :=
  (match parsedGuard? m with
    | some g => SyntaxEq.stmtsBeq (abiGuardBlock m) g | none => false) &&
  (match parsedMain? m with
    | some g => SyntaxEq.stmtsBeq main g | none => false)

/-- `constsCoherent` with the main block as a parameter (the emitter's output after WP-G1). -/
def constsCoherentWith (main : YulBlock) (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone && constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  decide (((expectedConsts pv m).map Prod.fst).Nodup) &&
  ((freeNames (abiGuardBlock m ++ main)).filter
      fun x => x != "vk" && x != "quotientEvaluator").all
    fun x => ((expectedConsts pv m).map Prod.fst).contains x

/-- **ONE BOOL FOR THE PROGRAM.** Everything about the emitted program that is decided by
    computation at a render: it is the parse of the text; its constant table is the plan view's;
    every call resolves; no binder shadows a constant; after inlining only the wrapper locals are
    free (guard block included); the transcript base is above Solidity's reserved words. -/
def programOkWith (main : YulBlock) (pv : PlanView) (m : Model) : Bool :=
  let consts := constTableOf m
  codegenStruct main m &&
  constsCoherentWith main pv m &&
  callsResolved main &&
  noShadow consts (abiGuardBlock m ++ wrapperLocals m 0 0 ++ main) &&
  (freeNames (Inline.inlineContractConstants consts (abiGuardBlock m ++ main))).all
    (fun x => x == "vk" || x == "quotientEvaluator") &&
  decide (0x80 ≤ pv.memory.transcriptMptr)

/-- The clause as it reads once `mainAsmRaw` is the WP-G1 emitter. -/
def programOk (pv : PlanView) (m : Model) : Bool := programOkWith (mainAsmRaw pv) pv m

/-- **VALIDITY, V3.** Seven clauses in four groups, replacing the thirteen of
    `Statements.lean:182-217` and the proposed pins D-P46 / D-P48. -/
structure Render.ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- G. Plan, compact quotient blocks and model are the generator's output for THIS constraint
      system, configuration, payload and DELTA. -/
  generated : R.GeneratedBy
  /-- G. The build inputs are the configuration's and the key's (frozen clause 5, unchanged). -/
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  /-- P. The program checks, one computation. -/
  program : programOk R.pv R.model = true
  /-- P. No world write (frozen clause 10, unchanged). -/
  noWriters : NoWriters (R.prog 0 0)
  /-- K. Field, domain and G2 parameters agree (frozen clause 8, unchanged). -/
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  /-- K. Every payload word is the Lean key's. -/
  payload : PayloadAgrees R
  /-- S. Scope (frozen clause 9; `wf.permutationCommitmentsMatch` repaired elsewhere). -/
  supported : SupportedV2 R

/-- What V3 gives the block proofs that V2 supplied pin by pin: a table lookup is a lookup in the
    DATA table, for EVERY valid render, with no string parsing in the proof. -/
theorem Render.ValidV3.vkMptr_const {R : Render p G₁ G₂ Gₜ} (h : R.ValidV3) :
    R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr) := by
  have hp := h.program
  simp only [programOk, programOkWith, Bool.and_eq_true] at hp
  have hc := hp.1.1.1.1.2
  simp only [constsCoherentWith, Bool.and_eq_true] at hc
  have heq := eq_of_beq hc.1.1.2
  show (constTableOf R.model).lookup "VK_MPTR" = _
  rw [heq]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;>
    simp [expectedConsts, h1, h2, h3, List.lookup, cAddr, ptrAddr, ptrValue]

/-- The same for the pin D-P48 asked to add to the frozen surface. -/
theorem Render.ValidV3.returnMptr_const {R : Render p G₁ G₂ Gₜ} (h : R.ValidV3) :
    R.consts.lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr := by
  have hp := h.program
  simp only [programOk, programOkWith, Bool.and_eq_true] at hp
  have hc := hp.1.1.1.1.2
  simp only [constsCoherentWith, Bool.and_eq_true] at hc
  have heq := eq_of_beq hc.1.1.2
  show (constTableOf R.model).lookup "RETURN_MPTR" = _
  rw [heq]
  cases h1 : R.model.expectedVkCodehash <;> cases h2 : R.model.quotientExternal <;>
    cases h3 : R.model.expectedQuotientCodehash <;>
    simp [expectedConsts, h1, h2, h3, List.lookup]

end Midfall.LoweringV2

/-! ## 7. Evaluation at the fixture, on the DERIVED render -/

namespace Fixture

open Midfall.Instances Midfall.Instances.PoseidonValid Midfall.Instances.PoseidonInputs
open Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonV2
open Midfall.LoweringV2 Midfall.Generator.PlanNew Midfall.Lowering.YulParse
open Midfall.Generator.ContractKats Midfall.Generator.VerifierPartialKats

/-- Fq::DELTA (curves/src/bls12_381/fq.rs:492); the contract literal at dump line 1975. -/
def blsDelta : Fr Yul.blsR :=
  (0x08634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7 : Fr Yul.blsR)

/-- The parsed payload plus the four reservation fields `vkModelFromArtifact` leaves empty. -/
def vkFull : Except Fault Halo2VerifyingKey := do
  let v := poseidonVkGen
  let hdr := (v.constants.filter fun c => c.1 != "quotient_const" && c.1 != "quotient_program").length
  let nC := (v.constants.filter fun c => c.1 == "quotient_const").length
  let nP := (v.constants.filter fun c => c.1 == "quotient_program").length
  let lay ← unwrapAt "scratch" (VkPayloadLayout.forVk hdr nC nP v.fixedComms.length v.permutationComms.length)
  let qc ← unwrapAt "scratch" (lay.wordOffset PayloadSectionKind.quotientConstants)
  let qp ← unwrapAt "scratch" (lay.wordOffset PayloadSectionKind.quotientProgram)
  pure { v with quotientConstOffsetWords := some qc, quotientConstWords := nC, quotientProgramOffsetWords := some qp, quotientProgramWords := nP }

def genWith (delta : Fr Yul.blsR) (f : Halo2VerifyingKey → Halo2VerifyingKey) : Except Fault GenOut :=
  vkFull >>= fun v =>
    generateAll Features.solidity delta poseidonVkExec poseidonConfig (f v) poseidonInputs poseidonFlags

def gen : Except Fault GenOut := genWith blsDelta id

def diffCount (a b : String) : Nat :=
  (((a.splitOn "\n").zip (b.splitOn "\n")).filter fun (x, y) => x != y).length

def textOf (o : GenOut) : String := renderHalo2Verifier (rootCtxOfVerifier o.model) (partsOf o.model)

def emitPcsScoped (pv : PlanView) : Block EVM.Op :=
  match Midfall.Lowering.GenAstPcs.computationsAst pv.meta_ pv.dat pv.memory pv.truncatedChallenges false with
  | .ok blocks => [Stmt.block (blocks.map Stmt.block)]
  | .error _ => []

/-- Stand-in for the WP-G1 emitter: today's emitters, pcs with its scopes, and the three
    un-emitted regions taken as the PARSE of the model's own text. -/
def mainV3 (pv : PlanView) (m : Model) : YulBlock :=
  let b := partialCtxOfVerifier m
  let P (t : String) : Block EVM.Op := (parseLines [t]).getD []
  mainGuardBlock ++ GenAst.emitHelpers pv ++ P (renderAccumulatorHelpers b) ++ mainLocals ++
    Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++
      (match q with
       | .quotientLin => P (renderQuotientHelpers b) ++ P (renderQuotientNumeratorBlock b) ++ GenAst.emitQuotientLin pv
       | .pcs => emitPcsScoped pv
       | q => GenAst.emitPartial pv q)

def report (e : Except Fault GenOut) (f : GenOut → String) : String :=
  match e with
  | .ok o => f o
  | .error (Fault.panic s) => "PANIC " ++ s
  | .error _ => "ERR"

-- 7.1 the generator runs, and its text is the artifact but for BUILD_ID
#eval report gen fun o =>
  s!"ok; text differs from the Rust artifact in {diffCount (textOf o) poseidonVerifierDump} line(s); len {(textOf o).length}/{poseidonVerifierDump.length}; proofLen={o.plan.proofLayout.proofLen}; vkMptr={pn o.plan.vkMptr}"
-- 7.2 the program clause at the derived render: with the V3 stand-in, and with today's emitter
#eval report gen fun o =>
  let pv := planViewOf o.plan o.model none
  s!"programOkWith mainV3 = {programOkWith (mainV3 pv o.model) pv o.model}; programOk (today's mainAsmRaw) = {programOk pv o.model}; noWriters = {Midfall.Yul.Bridge.noWritersFuel 20000 (Inline.inlineContractConstants (constTableOf o.model) (abiGuardBlock o.model ++ wrapperLocals o.model 0 0 ++ mainV3 pv o.model))}"
-- 7.3 the conjuncts of the program clause, separately
#eval report gen fun o =>
  let pv := planViewOf o.plan o.model none
  let main := mainV3 pv o.model
  s!"codegenStruct={codegenStruct main o.model} consts={constsCoherentWith main pv o.model} callsResolved={callsResolved main} noShadow={noShadow (constTableOf o.model) (abiGuardBlock o.model ++ wrapperLocals o.model 0 0 ++ main)} transcriptFloor={decide (0x80 ≤ pv.memory.transcriptMptr)}"
-- 7.4 the frozen clauses 1-3 at the generator's plan: 1 is FALSE, 2 and 3 are TRUE
#eval report gen fun o =>
  let c1 := match ConstraintSystemMeta.new Features.solidity poseidonVkExec.cs 1 with
    | .ok m => m == o.plan.meta_ | .error _ => false
  let c2 := match ProofCalldataLayout.fromProtocol o.plan.meta_.protocol abiVerifyProofProofCptr o.plan.meta_.numEvals o.plan.meta_.numPointSets with
    | .ok l => l.proofLen == o.plan.proofLayout.proofLen && l.proofEnd == o.plan.proofLayout.proofEnd | .error _ => false
  let c3 := match o.plan.validateGeneratorInvariants with | .ok (.ok ()) => true | _ => false
  s!"frozen circuitMeta={c1} layout={c2} invariants={c3}"
-- 7.5 FALSIFIER (delta): the placeholder delta 2 of poseidonE changes the generated text
#eval report (genWith 2 id) fun o =>
  s!"delta=2: ok; text differs from the artifact in {diffCount (textOf o) poseidonVerifierDump} line(s)"
-- 7.6 FALSIFIER (payload, quotient section): flip one quotient_program word -> the generator refuses
def flipProgWord (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { v with constants := v.constants.zipIdx.map fun (c, i) => if i == 33 then (c.1, c.2 + 1) else c }
#eval report (genWith blsDelta flipProgWord) fun _ => "ok (NOT refused)"
-- 7.7 NON-FALSIFIER (payload, header): flip omega (word 4) -> the generator still accepts, so
--     `PayloadAgrees` is needed in addition to `GeneratedBy`
def flipOmega (v : Halo2VerifyingKey) : Halo2VerifyingKey :=
  { v with constants := v.constants.zipIdx.map fun (c, i) => if i == 4 then (c.1, c.2 + 1) else c }
#eval report (genWith blsDelta flipOmega) fun o =>
  s!"omega flipped: generator ok; verifier text differs in {diffCount (textOf o) poseidonVerifierDump} line(s)"
-- 7.8 Except.getOk closes the model clause shape
example : gen = .ok (gen.getOk (by native_decide)) := Except.eq_ok_getOk _ _

end Fixture

#print axioms Except.eq_ok_getOk
#print axioms Midfall.LoweringV2.Render.ValidV3.vkMptr_const
#print axioms Midfall.LoweringV2.Render.ValidV3.returnMptr_const
#check @Midfall.LoweringV2.Render.ValidV3
#check @Midfall.LoweringV2.Render.GeneratedBy
#check @Midfall.LoweringV2.generateAll
#check @Midfall.Generator.PlanNew.newFromVk

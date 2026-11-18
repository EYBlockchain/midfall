/-
  Midfall.LoweringV2.Consts — ONE constants-coherence clause and its generic lookup lemmas (OBJ.4).

  WHAT THIS FILE IS. The blocks read their addresses out of the render's CONSTANT TABLE,
  `R.consts = constTableOf R.model`, which is the rendered `Constants.sol` parsed back as
  `(name, value)` pairs. For ~15 rounds every fact a block needed from that table was carried as a
  separate pin hypothesis — `vkPins.vkMptr`, `vkPins.payloadLen`, `vkProgressPins.vkLen`,
  `vkProgressPins.vkHash`, `trRetMptr`, D-P46's table half, D-P48. This file replaces them with
  DERIVATIONS: each is one lookup in the table, and a lookup in the render's table is a lookup in
  the DATA table `expectedConsts pv m`, which is what `constsCoherent` says the two are. Nothing
  here takes its own conclusion as a hypothesis.

  WHY THE FIVE DEFINITIONS ARE NOT HERE. The card's step 1 asks `Consts.lean` to contain `cAddr`,
  `expectedConsts`, `constLinesLiteral`, `progConstNames`, `constsCoherent`. Those five ALREADY
  EXIST in the tree — `Midfall/LoweringV2/Statements.lean` :516, :524, :637, :630, :654 — moved
  there by ST.6 (D-P67), not by this card. They had to move: `constsCoherent` is a conjunct of
  `programOkB`, `programOkB` is the `program` clause of the FROZEN `Render.Valid`, and a frozen
  statement may not rest on a refinable definition (D-P65, the same reason `Render.slices` and
  `Render.scope` moved). Re-declaring them here would duplicate the frozen text and let the two
  drift. So this file IMPORTS them and adds what was missing: the lookup lemmas, the two data facts
  they need, and the pin-bundle derivations. This file is refinable.

  WHAT THE LOOKUPS GIVE AND WHAT THEY CANNOT GIVE — stated here because it is the finding.
  `constsCoherent pv m` is five conjuncts; the third, `constTableOf m == expectedConsts pv m`, is
  the only one that mentions a VALUE. So it can only ever deliver: a lookup in the render's table
  equals a lookup in `expectedConsts pv m`. Every entry of `expectedConsts` is read off `pv` or
  `m` by construction, so each of the eight names the blocks needs resolves here (section 3). THREE
  of the eight are guarded by a match on `m.expectedVkCodehash`, because that is how the emitter
  writes them: `EXPECTED_VK_PAYLOAD_LENGTH`, `EXPECTED_VK_LENGTH`, `EXPECTED_VK_CODEHASH_WORD` are
  ABSENT from the table when the render has no VK-codehash arm. Their lemmas are therefore stated
  twice: an unconditional form that names the match, and a `some`-form under `Option.IsSome`.
  That `IsSome` is NOT a table fact and this file does not invent it: `Artifacts.lean:524` sets
  `expectedVkCodehash := if flags.separate then some _ else none`, so its source is
  `SupportedV2.separateVk` TOGETHER WITH the `generated` clause — a lemma about what `generateAll`
  puts in the model, which is OBJ.7/RECON.1b's, not a lookup.

  TWO OF THE SIX PINS ARE NOT TABLE FACTS AT ALL, and no lemma in this file can produce them:
  * `vkPins.numInst` is `R.pv.numInstances = R.cfg.numInstances`. `pv.numInstances` IS
    `R.model.numInstances` (`Render.pv_numInstances` below, by `rfl`), so the pin says the MODEL's
    instance count is the CONFIGURATION's — a generator-spec fact whose only source in `Valid` is
    `generated`. No constant name appears in it.
  * `vkPins.disjoint` is an inequality between two plan-view addresses with a payload length in it.
    It mentions no constant, so `constsCoherent` cannot see it. Its plausible source is
    `SupportedV2.layout` (`memory.map.WellFormed`, `Layout.lean:1127`), a disjointness claim about
    the layout MAP; reaching these two windows needs a layout lemma.
  RECON.1b reached the same conclusion from the other direction. Section 4 records it as two
  reductions rather than as an opinion, and section 5 turns the four REAL table facts into the two
  pin structures so the residual premises are exactly those two plus the codehash arm.

  A NUMBER ONLY THE MODEL CARRIES CANNOT BE FALSIFIED HERE, and that is by construction, not an
  oversight: `G1MSM_GAS_SMOKE` (`m.constructorG1msmSmokeGas`) and `ACC_RHS_MSM_GAS`
  (`m.accRhsMsmGas`) are rendered into the text from the same `Model` field `expectedConsts`
  reads, so mutating the field moves BOTH sides of conjunct 3 together. Same for the gas schedule
  under `m.templateConstants.gas`. What conjunct 3 CAN catch is a disagreement between the table and
  the PLAN VIEW — an address, a payload length, a calldata pointer — and those are the facts the
  blocks need. The falsifiers at the bottom print `true` for a smoke-gas perturbation and `false`
  for every plan-view perturbation, which is this paragraph as data.

  NO `sorry` IN THIS FILE.
-/
import Midfall.LoweringV2.Statements

namespace Midfall.LoweringV2

open Midfall Midfall.Generator Midfall.Lowering
open YulSemantics YulSemantics.EVM

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- **THE VK-CODEHASH ARM.** Three of the eight entries of `expectedConsts` are written only when the
    render has a VK-codehash check, so their lookups need this and nothing else. It is NOT a table
    fact and this file does not derive it: `Artifacts.lean:524` sets
    `expectedVkCodehash := if flags.separate then some _ else none`, so its source is
    `SupportedV2.separateVk` plus a lemma about what `generateAll` puts in the model — the
    `generated` clause, OBJ.7/RECON.1b's, not `constsCoherent`. -/
def vkCodehashArm (m : Model) : Prop := ∃ x, m.expectedVkCodehash = some x

/-! ## 1. THE TWO DATA FACTS THE LOOKUPS NEED

  Neither is a table fact. Both were missing, and RECON.1b named them: "`payloadLen`/`vkLen`/
  `vkHash` need a data fact". Here they are, sorry-free, with no `native_decide`. -/

/-- `cAddr` (frozen, `Statements.lean:516`) and `Inv.ptrAddr` are the same adapter: `ptrValue` is
    the projection. This is what lets the derived `VK_MPTR` lookup be stated at the shape the pin
    uses, `ptrAddr R.pv.memory.vkMptr`, with no change of meaning. -/
theorem cAddr_eq_ptrAddr (q : Ptr) : cAddr q = ptrAddr q := rfl

/-- The one byte-emitting loop of `natToBytesLowFirst` writes exactly `len` bytes whatever `n` is:
    each step pushes one byte and recurses on `len - 1`. -/
theorem natToBytesLowFirst_go_size :
    ∀ (len : Nat) (n : Nat) (acc : Bytes), (natToBytesLowFirst.go n len acc).size = len + acc.size
  | 0, _, acc => by rw [natToBytesLowFirst.go.eq_1]; omega
  | k + 1, n, acc => by
      rw [natToBytesLowFirst.go.eq_2,
        natToBytesLowFirst_go_size k (n / 256) (acc.push (n % 256).toUInt8),
        ByteArray.size_push]
      omega

/-- `natToBytesLowFirst n len` is `len` bytes. -/
theorem natToBytesLowFirst_size (n len : Nat) : (natToBytesLowFirst n len).size = len := by
  show (natToBytesLowFirst.go n len Bytes.empty).size = len
  have h : (Bytes.empty : Bytes).size = 0 := rfl
  rw [natToBytesLowFirst_go_size, h]
  omega

/-- `natToBytesBE n len` is `len` bytes: reversing a list does not change its length. -/
theorem natToBytesBE_size (n len : Nat) : (natToBytesBE n len).size = len := by
  show ((natToBytesLowFirst n len).data.toList.reverse.toArray).size = len
  have h1 : ((natToBytesLowFirst n len).data.toList.reverse.toArray).size =
      ((natToBytesLowFirst n len).data.toList.reverse).length := rfl
  rw [h1, List.length_reverse]
  have h2 : ((natToBytesLowFirst n len).data.toList).length = (natToBytesLowFirst n len).size := rfl
  rw [h2, natToBytesLowFirst_size]

/-- Every `wordToBytesBE` is exactly 32 bytes — the fixed-width `to_bytes` of the Rust port. -/
theorem wordToBytesBE_size (w : Word256) : (wordToBytesBE w).size = 32 :=
  natToBytesBE_size _ _

/-- `ByteArray.append` adds sizes (core states `size_append` for the `++` spelling). -/
theorem bytes_append_size (a b : Bytes) : (a.append b).size = a.size + b.size := by
  show (a ++ b).size = a.size + b.size
  rw [ByteArray.size_append]

/-- The payload emitter writes 32 bytes per word and nothing else. -/
theorem foldl_wordToBytesBE_size : ∀ (ws : List Word256) (acc : Bytes),
    (ws.foldl (fun acc w => acc.append (wordToBytesBE w)) acc).size = acc.size + 32 * ws.length
  | [], acc => by simp
  | w :: ws, acc => by
      rw [List.foldl_cons, foldl_wordToBytesBE_size ws _, bytes_append_size, wordToBytesBE_size,
        List.length_cons]
      omega

/-- Each EIP-2537-padded commitment contributes exactly 4 words = 128 bytes. -/
theorem flatMap_G1Words_len (l : List G1Words) :
    (l.flatMap fun w => [w.xHi, w.xLo, w.yHi, w.yLo]).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

/-- **DATA FACT 1 OF 2.** The payload the VK window holds is `vk.len` bytes: `bytes` writes 32
    bytes per scalar constant and 4 words per EIP-2537-padded commitment, and `len`
    (`Models.lean:462`) counts exactly that. `Models.lean:1210` KATs this at ONE synthetic key;
    this is the general statement, and it is what `EXPECTED_VK_PAYLOAD_LENGTH` needs. -/
theorem Halo2VerifyingKey.bytes_size (vk : Halo2VerifyingKey) : vk.bytes.size = vk.len := by
  unfold Halo2VerifyingKey.bytes
  show ((vk.constants.map (·.2) ++
      vk.fixedComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo]) ++
      vk.permutationComms.flatMap (fun w => [w.xHi, w.xLo, w.yHi, w.yLo])).foldl
      (fun acc w => acc.append (wordToBytesBE w)) Bytes.empty).size = _
  rw [foldl_wordToBytesBE_size, List.length_append, List.length_append, List.length_map,
    flatMap_G1Words_len, flatMap_G1Words_len]
  have h0 : (Bytes.empty : Bytes).size = 0 := rfl
  rw [h0]
  unfold Halo2VerifyingKey.len
  omega

/-- The `0xfe` prefix is one byte. -/
theorem vkRuntimePrefix_size :
    (ByteArray.push Bytes.empty (Nat.toUInt8 vkRuntimePrefix)).size = 1 := by
  rw [ByteArray.size_push]
  have h : (Bytes.empty : Bytes).size = 0 := rfl
  rw [h]

/-- The runtime payload is the `0xfe` prefix byte and then the payload. -/
theorem Halo2VerifyingKey.runtimeBytes_size (vk : Halo2VerifyingKey) :
    vk.runtimeBytes.size = vk.len + 1 := by
  unfold Halo2VerifyingKey.runtimeBytes
  rw [bytes_append_size, vkRuntimePrefix_size, Halo2VerifyingKey.bytes_size]
  omega

/-- **DATA FACT 2 OF 2.** The plan view's key IS the render's plan key: `planViewOf` passes `L.vk`
    straight through (`Program.lean:47-49`), so `pv.vk` and `R.plan.vk` are one value and the
    pin's `R.plan.vk.runtimeBytes.size` and the table's `pv.vk.len + 1` are about the same key. -/
theorem Render.pv_vk (R : Render p G₁ G₂ Gₜ) : R.pv.vk = R.plan.vk := rfl

theorem Render.pv_numInstances (R : Render p G₁ G₂ Gₜ) :
    R.pv.numInstances = R.model.numInstances := rfl

/-! ## 2. THE COHERENCE PROJECTION, GENERIC IN THE PLAN VIEW AND THE MODEL

  `Statements.lean:930` already has the render-level half (`lookup_expectedConsts_of_programOkB`),
  which digs the third conjunct out of `programOkB` by a positional projection. The card asks for
  `consts_lookup_of_coherent`: the same transfer stated on the clause itself, so a consumer that has
  `constsCoherent` need not know where it sits inside `programOkCore`. -/

/-- The clause as a `Prop`. `.Nodup` is a `Prop`, so the clause wraps it in `decide`; the card's
    Guidance says the same about printing it. -/
def ConstsCoherent (pv : PlanView) (m : Model) : Prop := constsCoherent pv m = true

/-- **THE GENERIC TRANSFER.** Under `constsCoherent`, a lookup in the table the render READS is a
    lookup in the table the plan view SAYS. No string parsing, no fixture, no `native_decide`: the
    third conjunct is a `BEq` equality of the two lists and `eq_of_beq` turns it into a rewrite. -/
theorem consts_lookup_of_coherent {pv : PlanView} {m : Model} (h : ConstsCoherent pv m)
    (name : String) : (constTableOf m).lookup name = (expectedConsts pv m).lookup name := by
  have h3 : (constTableOf m == expectedConsts pv m) = true := by
    unfold ConstsCoherent constsCoherent at h
    simp only [Bool.and_eq_true] at h
    exact h.1.1.2
  rw [eq_of_beq h3]

/-- The same transfer from the render's program clause, packaged so a block row cites one name. -/
theorem consts_lookup_of_valid {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) (name : String) :
    R.consts.lookup name = (expectedConsts R.pv R.model).lookup name :=
  lookup_expectedConsts_of_programOkB (programOkB_of_valid hR) name

/-! ## 3. THE EIGHT LOOKUPS

  Each is proved by the six-line script of `ObjectV3Full.lean:247-257`: transfer through coherence,
  then case-split the four optional arms of the model and let `List.lookup` do the rest. Five are
  unconditional. Three are guarded by the VK-codehash arm and are stated twice — the match form,
  which needs nothing, and the `some` form, which needs only `IsSome`.

  `#print axioms` at the bottom of the file: every one is the standard three. -/

/-- `VK_MPTR` — the address the `.vkLoading` block copies the payload to. Unconditional: the entry
    is in the table for every plan view and every model, and its value is the plan view's own
    pointer. This is `vkPins.vkMptr`, derived. -/
theorem expectedConsts_lookup_VK_MPTR (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "VK_MPTR" = some (cAddr pv.memory.vkMptr) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `RETURN_MPTR` — the window the TraceReturn block writes its verdict into. Unconditional. This is
    `trRetMptr`, derived, and it is why `tr_blockRow` no longer needs a pin. -/
theorem expectedConsts_lookup_RETURN_MPTR (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "RETURN_MPTR" = some pv.memory.verifierReturnMptr := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `TRANSCRIPT_MPTR` — the transcript region base. Unconditional. (`Statements.lean:918` already
    carried this one inside the three-name bundle `expectedConsts_lookups`; restated singly here so
    the eight read as one family.) -/
theorem expectedConsts_lookup_TRANSCRIPT_MPTR (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "TRANSCRIPT_MPTR" = some pv.memory.transcriptMptr := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `NUM_INSTANCE_CPTR` — the calldata word `decodeCalldata` reads the instance count from.
    Unconditional, and it is the entry the `.vkLoading` length clause turns into `Inv .vk`'s
    calldata fact. -/
theorem expectedConsts_lookup_NUM_INSTANCE_CPTR (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "NUM_INSTANCE_CPTR" = some pv.proofLayout.proofEnd := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `FR_MODULUS` — the field constant. Unconditional as a table entry; the equation
    `frModulusConstant = p` is NOT a table fact and comes from `EnvAgrees.modulus`
    (`Statements.lean:942`, `frModulus_of_programOk_of_modulus`). -/
theorem expectedConsts_lookup_FR_MODULUS (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "FR_MODULUS" = some frModulusConstant := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- The three VK-arm entries, as ONE match: present exactly when the render has a VK-codehash arm. -/
theorem expectedConsts_lookup_vkArm (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "EXPECTED_VK_PAYLOAD_LENGTH" =
      (match m.expectedVkCodehash with | some _ => some pv.vk.len | none => none) ∧
    (expectedConsts pv m).lookup "EXPECTED_VK_LENGTH" =
      (match m.expectedVkCodehash with
        | some _ => some (pv.vk.len + 1) | none => none) ∧
    (expectedConsts pv m).lookup "EXPECTED_VK_CODEHASH_WORD" =
      (match m.expectedVkCodehash with
        | some _ => some (keccak256 pv.vk.runtimeBytes).toNat | none => none) := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- `EXPECTED_VK_PAYLOAD_LENGTH` under the arm: the table's payload length IS the payload's own
    length. This is `vkPins.payloadLen`, derived. -/
theorem expectedConsts_lookup_EXPECTED_VK_PAYLOAD_LENGTH (pv : PlanView) (m : Model)
    (h : vkCodehashArm m) :
    (expectedConsts pv m).lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some pv.vk.len := by
  obtain ⟨x, hx⟩ := h
  have key := expectedConsts_lookup_vkArm pv m
  simp only [hx] at key
  exact key.1

/-- `EXPECTED_VK_LENGTH` under the arm: the runtime length is the payload length plus the `0xfe`
    prefix — `runtimeBytes_size`, the data fact, not a hypothesis. -/
theorem expectedConsts_lookup_EXPECTED_VK_LENGTH (pv : PlanView) (m : Model)
    (h : vkCodehashArm m) :
    (expectedConsts pv m).lookup "EXPECTED_VK_LENGTH" = some pv.vk.runtimeBytes.size := by
  obtain ⟨x, hx⟩ := h
  have key := expectedConsts_lookup_vkArm pv m
  simp only [hx] at key
  rw [key.2.1, Halo2VerifyingKey.runtimeBytes_size]

/-- `EXPECTED_VK_CODEHASH_WORD` under the arm: the table's codehash word is `keccak256` of the
    runtime bytes. -/
theorem expectedConsts_lookup_EXPECTED_VK_CODEHASH_WORD (pv : PlanView) (m : Model)
    (h : vkCodehashArm m) :
    (expectedConsts pv m).lookup "EXPECTED_VK_CODEHASH_WORD" =
      some (keccak256 pv.vk.runtimeBytes).toNat := by
  obtain ⟨x, hx⟩ := h
  have key := expectedConsts_lookup_vkArm pv m
  simp only [hx] at key
  exact key.2.2

/-! ### The same eight at a render, from `Render.Valid` alone

  These are the names a block row cites. Each is one transfer (`consts_lookup_of_valid`) plus one
  lookup above. No fixture, no `native_decide`, no pin. -/

/-- **THE DERIVED `vkPins.vkMptr`.** -/
theorem consts_lookup_VK_MPTR {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr) := by
  rw [consts_lookup_of_valid hR, expectedConsts_lookup_VK_MPTR, cAddr_eq_ptrAddr]

/-- **THE DERIVED `trRetMptr`, and more than it: the pin only asked for an `∃`.** -/
theorem consts_lookup_RETURN_MPTR {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    R.consts.lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr :=
  consts_lookup_of_valid hR "RETURN_MPTR" ▸ expectedConsts_lookup_RETURN_MPTR _ _

/-- The derived `Valid.transcriptMptr` lookup half, restated singly. -/
theorem consts_lookup_TRANSCRIPT_MPTR {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    R.consts.lookup "TRANSCRIPT_MPTR" = some R.pv.memory.transcriptMptr :=
  consts_lookup_of_valid hR "TRANSCRIPT_MPTR" ▸ expectedConsts_lookup_TRANSCRIPT_MPTR _ _

/-- The calldata pointer the `.vkLoading` length clause needs. -/
theorem consts_lookup_NUM_INSTANCE_CPTR {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    R.consts.lookup "NUM_INSTANCE_CPTR" = some R.pv.proofLayout.proofEnd :=
  consts_lookup_of_valid hR "NUM_INSTANCE_CPTR" ▸ expectedConsts_lookup_NUM_INSTANCE_CPTR _ _

/-- `FR_MODULUS` as a table entry; `= p` needs `hR.env.modulus` on top (D-P71 addition 6). -/
theorem consts_lookup_FR_MODULUS {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    R.consts.lookup "FR_MODULUS" = some frModulusConstant :=
  consts_lookup_of_valid hR "FR_MODULUS" ▸ expectedConsts_lookup_FR_MODULUS _ _

/-- **THE DERIVED `vkPins.payloadLen`.** Needs the codehash arm, and says so. -/
theorem consts_lookup_EXPECTED_VK_PAYLOAD_LENGTH {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R)
    (h : vkCodehashArm R.model) :
    R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some R.pv.vk.len := by
  rw [consts_lookup_of_valid hR, expectedConsts_lookup_EXPECTED_VK_PAYLOAD_LENGTH _ _ h]

/-- **THE DERIVED `vkProgressPins.vkLen`.** -/
theorem consts_lookup_EXPECTED_VK_LENGTH {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R)
    (h : vkCodehashArm R.model) :
    R.consts.lookup "EXPECTED_VK_LENGTH" = some R.plan.vk.runtimeBytes.size := by
  rw [consts_lookup_of_valid hR, expectedConsts_lookup_EXPECTED_VK_LENGTH _ _ h,
    ← Render.pv_vk R]

/-- **THE DERIVED `vkProgressPins.vkHash`.** -/
theorem consts_lookup_EXPECTED_VK_CODEHASH_WORD {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R)
    (h : vkCodehashArm R.model) :
    R.consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some (keccak256 R.plan.vk.runtimeBytes).toNat := by
  rw [consts_lookup_of_valid hR, expectedConsts_lookup_EXPECTED_VK_CODEHASH_WORD _ _ h,
    ← Render.pv_vk R]

/-! ## 4. THE RESIDUAL: WHAT `constsCoherent` CANNOT GIVE, AS TWO REDUCTIONS

  Not opinions — statements that exhibit the shape of the two remaining pins. -/

/-- `vkPins.numInst` REWRITES to a statement about the model and the configuration. There is no
    constant name in it, so no lookup lemma can produce it: its source is the `generated` clause
    together with a lemma that `generateAll` copies `cfg.numInstances` into the model
    (`Generated.lean:135` is where that copy happens). OBJ.7/RECON.1b's, not a table fact. -/
theorem vkPins_numInst_is_not_a_table_fact (R : Render p G₁ G₂ Gₜ) :
    (R.pv.numInstances = R.cfg.numInstances) = (R.model.numInstances = R.cfg.numInstances) := by
  simp [Render.pv_numInstances]

/-- `vkPins.disjoint` mentions only plan-view addresses and the payload length: no constant, no
    table, nothing for `constsCoherent` to compare. Its source is `SupportedV2.layout`
    (`memory.map.WellFormed`, `Layout.lean:1127`), a disjointness claim about the layout MAP;
    reaching these two windows needs a layout lemma. NOT a table fact. -/
theorem vkPins_disjoint_is_not_a_table_fact (R : Render p G₁ G₂ Gₜ) :
    (ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
      ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr) =
    (cAddr R.pv.memory.g1IdentityMptr + 128 ≤ cAddr R.pv.memory.vkMptr ∨
      cAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ cAddr R.pv.memory.g1IdentityMptr) := by
  simp [cAddr_eq_ptrAddr]

/-! ## 5. THE PIN BUNDLES, ASSEMBLED FROM THE DERIVATIONS

  **THEY MOVED HERE IN OBJ.8 STEP 4 (D-P67).** `vkPins` and `vkProgressPins` used to be declared in
  `Statements.lean` section 2 - first as clauses 12-13 of `Render.Valid` (D-P50/S.9), then, after
  ST.6 cut `Valid` over to the seven V3 clauses, as two frozen structures that were not clauses of
  anything. OBJ.8 deletes them from the frozen surface, and this is where they land: they are a
  REFINABLE PREMISE BUNDLE of one block row, not a statement of the theory. Field for field the
  text is unchanged - same six fields, same order, same names, same types - so `Blocks/VkLoading.lean`
  and `Instances/PoseidonPins.lean` keep citing exactly what they cited. What changed is only which
  file is allowed to be edited without a re-hash, which is exactly what D-P67 was for.

  WHAT THEY STILL ASK FOR, AND WHY. Four of the six fields are theorems of `program`
  (`constsCoherent`), and this section derives all four. Two are not table facts at all, and no
  lemma here can produce them: `numInst` (section 4, `vkPins_numInst_is_not_a_table_fact`) and
  `disjoint` (section 4, `vkPins_disjoint_is_not_a_table_fact`). A third fact gates the three
  guarded lookups: `vkCodehashArm R.model`. Those THREE are the residuals OBJ.8's report names as
  rows (a), (b) and (c); they are premises of `vk_blockRow`, not clauses of `Valid`, and adding a
  clause to `Valid` to make them close is the one move the card forbids. -/

/-- **THE FOUR `vkLoading` RENDER PINS (D-P50; the text is S.4's `Blocks/VkLoading.lean` section 5,
    moved to `Statements.lean` by S.9 and back out again by OBJ.8 step 4 - see §5 above and
    `Statements.lean` §2B). `Clean R .vk` postulates `Inv .vk`, whose first clause pins memory at
    `ptrAddr R.pv.memory.vkMptr` to `R.pv.vk.bytes`, and the block writes to the inlined `VK_MPTR`
    and copies `EXPECTED_VK_PAYLOAD_LENGTH` bytes. Nothing in `Frame`, `Clean`, `Inv` or any other
    `Valid` clause says the render's CONSTANT TABLE agrees with its own PLAN VIEW about where that
    window is, how long the payload is, and how many instances the calldata carries - and without
    pins 1, 2 and 4 `BlockSound R .vkLoading` is FALSE, not merely unproved: a render whose table
    points `VK_MPTR` elsewhere copies the payload to the wrong address, exits `normal` with
    `success = 1`, and satisfies neither `Clean .vk` nor `Poisoned`. Each is a computation at a
    real deployment, and S.8 PROVED all four at `poseidonRender` sorry-free
    (`Instances/PoseidonPins.lean`). -/
structure vkPins (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- The table's VK window is the plan view's VK window. -/
  vkMptr : ∃ m, R.consts.lookup "VK_MPTR" = some m ∧ m = ptrAddr R.pv.memory.vkMptr
  /-- The table's payload length is the payload's own length. -/
  payloadLen : ∃ m, R.consts.lookup "EXPECTED_VK_PAYLOAD_LENGTH" = some m ∧ m = R.pv.vk.len
  /-- The plan view's instance count is the configuration's, which is the one `decodeCalldata`
      was called with. -/
  numInst : R.pv.numInstances = R.cfg.numInstances
  /-- The VK window does not overlap the g1_identity window `Inv` pins to zero at every
      checkpoint. -/
  disjoint : ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
    ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr

/-- The two MORE the `.vkLoading` PROGRESS half needs (D-P50; S.4's `Blocks/VkLoading.lean`
    section 5, moved with `vkPins`). The guard of the block's first statement has to be PASSABLE,
    which is a fact about the table and the deployed runtime rather than about any run: soundness
    gets it from the run, progress has to exhibit one. S.8 PROVED both at `poseidonRender`
    sorry-free (`Instances/PoseidonPins.lean`). -/
structure vkProgressPins (R : Render p G₁ G₂ Gₜ) : Prop where
  vkLen : ∃ m, R.consts.lookup "EXPECTED_VK_LENGTH" = some m ∧ m = R.plan.vk.runtimeBytes.size
  vkHash : ∃ m, R.consts.lookup "EXPECTED_VK_CODEHASH_WORD" = some m ∧
    m = (keccak256 R.plan.vk.runtimeBytes).toNat


/-- The four table-fact fields of `vkPins`, derived; the two residual fields named by hypothesis. -/
theorem vkPins_of_valid (R : Render p G₁ G₂ Gₜ) (hR : Render.Valid R)
    (hcode : vkCodehashArm R.model)
    (hnum : R.pv.numInstances = R.cfg.numInstances)
    (hdisj : ptrAddr R.pv.memory.g1IdentityMptr + 128 ≤ ptrAddr R.pv.memory.vkMptr ∨
      ptrAddr R.pv.memory.vkMptr + R.pv.vk.len ≤ ptrAddr R.pv.memory.g1IdentityMptr) :
    vkPins R :=
  { vkMptr := ⟨_, consts_lookup_VK_MPTR hR, rfl⟩
    payloadLen := ⟨_, consts_lookup_EXPECTED_VK_PAYLOAD_LENGTH hR hcode, rfl⟩
    numInst := hnum
    disjoint := hdisj }

/-- Both progress pins, derived: `vkProgressPins` has NO non-table field at all. -/
theorem vkProgressPins_of_valid (R : Render p G₁ G₂ Gₜ) (hR : Render.Valid R)
    (hcode : vkCodehashArm R.model) :
    vkProgressPins R :=
  { vkLen := ⟨_, consts_lookup_EXPECTED_VK_LENGTH hR hcode, rfl⟩
    vkHash := ⟨_, consts_lookup_EXPECTED_VK_CODEHASH_WORD hR hcode, rfl⟩ }

/-- The TraceReturn pin, derived outright: `RETURN_MPTR` is unconditional, so `trRetMptr` is no
    longer anything a row has to be given. -/
theorem trRetMptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : Render.Valid R) :
    ∃ m, R.consts.lookup "RETURN_MPTR" = some m :=
  ⟨_, consts_lookup_RETURN_MPTR hR⟩

end Midfall.LoweringV2


/-! ## 6. AXIOM REGISTER FOR THIS FILE

  Every lemma above is sorry-free and closes under the standard three. `#print axioms` is part of the
  file so the gate sees it, and D-P71 keeps `native_decide` out of `lowering_correct`'s cone: none of
  these use it. -/

#print axioms Midfall.LoweringV2.natToBytesLowFirst_go_size
#print axioms Midfall.LoweringV2.Halo2VerifyingKey.bytes_size
#print axioms Midfall.LoweringV2.Halo2VerifyingKey.runtimeBytes_size
#print axioms Midfall.LoweringV2.cAddr_eq_ptrAddr
#print axioms Midfall.LoweringV2.consts_lookup_of_coherent
#print axioms Midfall.LoweringV2.consts_lookup_of_valid
#print axioms Midfall.LoweringV2.expectedConsts_lookup_VK_MPTR
#print axioms Midfall.LoweringV2.expectedConsts_lookup_RETURN_MPTR
#print axioms Midfall.LoweringV2.expectedConsts_lookup_TRANSCRIPT_MPTR
#print axioms Midfall.LoweringV2.expectedConsts_lookup_NUM_INSTANCE_CPTR
#print axioms Midfall.LoweringV2.expectedConsts_lookup_FR_MODULUS
#print axioms Midfall.LoweringV2.expectedConsts_lookup_vkArm
#print axioms Midfall.LoweringV2.consts_lookup_VK_MPTR
#print axioms Midfall.LoweringV2.consts_lookup_RETURN_MPTR
#print axioms Midfall.LoweringV2.consts_lookup_TRANSCRIPT_MPTR
#print axioms Midfall.LoweringV2.consts_lookup_NUM_INSTANCE_CPTR
#print axioms Midfall.LoweringV2.consts_lookup_FR_MODULUS
#print axioms Midfall.LoweringV2.consts_lookup_EXPECTED_VK_PAYLOAD_LENGTH
#print axioms Midfall.LoweringV2.consts_lookup_EXPECTED_VK_LENGTH
#print axioms Midfall.LoweringV2.consts_lookup_EXPECTED_VK_CODEHASH_WORD
#print axioms Midfall.LoweringV2.vkPins_numInst_is_not_a_table_fact
#print axioms Midfall.LoweringV2.vkPins_disjoint_is_not_a_table_fact
#print axioms Midfall.LoweringV2.vkPins_of_valid
#print axioms Midfall.LoweringV2.vkProgressPins_of_valid
#print axioms Midfall.LoweringV2.trRetMptr_of_valid

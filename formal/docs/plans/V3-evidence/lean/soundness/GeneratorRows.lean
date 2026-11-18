/-
  GeneratorRows.lean  (SCRATCH - D-P71: the block rows restated for EVERY render)

  Typechecked against the built tree at cf00592 the way `V3-evidence/check.sh` compiles a file of
  `lean/soundness/` (see `check-rows.sh` next to this file): `SoundnessV3` and `StatementsV3` are
  compiled to interfaces in a private `V3_OUT`, then this file with `--root`.

  WHAT IS HERE
    §0  Vocabulary shared by the child lemmas (word operations, segments of an inlined block).
    §1  `rows_correct` (`ExitOk`, `SimContracts`, `ProgContracts`; NO `SimPins` conjunct) and the
        PROVED corollaries: the generic headline needs nothing beyond the rows and the headline's
        own codec laws. Totality is `rows_total` (= `total_correct`, §10).
    §2  PREMISE GAPS, each as a typechecked `def` that is NEVER a hypothesis of a row, and one
        PROVED finding: `SimPins` is not a consequence of `Valid` (which is why `rows_correct`
        does not conclude it).
    §3  HLP.1 generic: "the scope of every render defines helper `f` with this body".
    §4  Prefix (SIM.6).            §5  Lagrange (T3.9).        §6  TranscriptParser (ROW.TP).
    §7  QuotientLin (ROW.Q).       §8  PCS (ROW.PCS).          §9  FinalPairing (ROW.FP).
    §10 Totality (TOT.1), generic, with the composition PROVED from named leaves.

  RULES FOLLOWED
    * No existing definition is restated. `BlockSim`, `BlockProgS`, `StageInv`, `SimPins`,
      `SimContracts`, `ProgContracts`, `lowering_equivalence_of_stages` are `SoundnessV3`'s.
    * Every child lemma is an all-runs (`StmtsContractAll`) or existence (`StmtsContract`) fact about
      the OUTPUT OF AN EMITTER, constants inlined at an arbitrary table. `StmtsContractAll funs b pre
      post` is `∀ V st, pre V st → AllRuns funs V st b (post V st)` (prooftech/WPTac.lean:26), so the
      statements do not depend on whether `wp_run` executes parametric slices (GEN.0).
    * A fact about the render that neither the block nor `Valid` supplies is NOT added as a
      hypothesis of a row. It is recorded in §2 as `PG_*`. The rows of §4-§9 are therefore not
      provable from `R.Valid` as it stands today; each says which `PG_*` it waits for.
    * `R.Valid` is the name in the tree. After RECON.1/RECON.2 every `(hR : R.Valid)` below becomes
      `(hR : R.ValidV3)`, `SimPins R` is derived (`simPins_of_laws`), `EntryFrame` becomes
      `EntryFrameV3`, and the `PG_*` of §2 marked [V3] become projections of `hR`.

  RECON.1b STATUS — **THIS FILE IS NOT REBASED, AND IT IS NOT TYPECHECKED.** Two independent causes,
  neither of them this card's edit:
    (i) Its import `SoundnessV3.lean` does not elaborate at HEAD (3 errors: `R.scope c g` now
        unfolds to `hoist … (R.prog vkAddr 0)`, not `hoist … R.helpers` — ST.3 landed the scope
        after this file was written — and `lowering_equivalence_of_stages`' anonymous constructor
        predates ST.4's fourth conjunct). Until that file is rebased nothing here can be checked,
        and RECON.1b will not blind-edit 1381 lines it cannot compile.
    (ii) ST.6 cut the frozen `Render.Valid` over to the seven clauses, so §2's
        `breakCompressed_valid` still projects `hR.slots`, `hR.vkPins` and `hR.vkProgressPins`
        — clauses that no longer exist. `simPins_not_of_valid` cites the same bundle.
  THE PROJECTION MAP for whoever rebases it (each is a theorem of the single text, proved in
  `Midfall/LoweringV3/Statements.lean`): PG-NOSHADOW → `noShadow_of_programOk (programOkB_of_valid hR)`;
  PG-CONSTS-LAG and PG-CONSTS-TP → `expectedConsts_lookups` + `lookup_expectedConsts_of_programOkB`;
  PG-FRMOD → `frModulus_of_valid`; PG-NEGLAG → `negLagranges_of_valid`; PG-G1ID →
  `g1IdentityFloor_of_valid`; PG-EXIT → `exitDiscipline_of_valid` + `exitShape_of_exitDiscipline`;
  PG-G2SLOTS → `hR.payload.g2Base` / `.negSG2` with `hR.env`. **NO projection exists for
  PG-PCS-EMIT** (a generator lemma, still unowned) **or for the `vkPins`/`vkProgressPins` pair** —
  see the RECON.1b-PINS obligation recorded in `object/GeneratorCertified.lean` §5: those two
  bundles are NOT derivable from the single text today, so the `.vkLoading` row keeps them as free
  premises. That is a finding about the class, not an obstacle.

  `sorry` REGISTER: printed by `#cone_sorries` at the end; every one is a named theorem.
-/
import SoundnessV3
import StatementsV3
import Midfall.LoweringV2.Blocks.FinalPairing
import Midfall.Lowering.QvmFold

set_option autoImplicit false

namespace Midfall.LoweringV2.V3.Gen

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV2.V3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-! ## 0. Vocabulary -/

open Lean Elab Tactic Meta in
/-- Close `a = b` by `Eq.refl`, leaving the definitional check to the KERNEL. The elaborator's
    `rfl` runs `Meta.whnf`, which exceeds the default heartbeats on an inlined 28-statement block
    (measured here); the kernel reducer does not. No axiom is added. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  let some (_, _, rhs) := t.eq? | throwError "kernel_rfl: the goal is not an equality"
  goal.assign (← mkEqRefl rhs)

/-- Statements `i .. i + j - 1` of a block. A child lemma is about one segment of an inlined
    emitter output; its card's first step is the `rfl` that turns the segment into an explicit
    statement list (the `vk_slice_raw` move, Blocks/VkLoading.lean:164). -/
def seg (b : Block EVM.Op) (i j : Nat) : Block EVM.Op := (b.drop i).take j

/-- EVM `mulmod` as the dialect computes it (EVMExec.lean:722). Name fixed by card T3.8. -/
def wMulmod (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % n.toNat)

/-- EVM `addmod` as the dialect computes it (EVMExec.lean:721). Name fixed by card T3.8. -/
def wAddmod (a b n : U256) : U256 :=
  if n = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % n.toNat)

/-- `k` squarings: the word the loop `x_n := mulmod(x_n, x_n, r)` leaves after `k` iterations. -/
def wPow2 (r : U256) : Nat → U256 → U256
  | 0, x => x
  | k + 1, x => wPow2 r k (wMulmod x x r)

/-- The walk `w, w·ω, w·ω², …` of `pow_of_omega := mulmod(pow_of_omega, omega, r)`. -/
def omegaPows (r omega w0 : U256) : Nat → U256
  | 0 => w0
  | i + 1 => wMulmod (omegaPows r omega w0 i) omega r

/-- Memory agrees outside the window `[lo, lo + len)`. -/
def MemSameOutside (st st' : EvmState) (lo len : Nat) : Prop :=
  ∀ a, (a < lo ∨ lo + len ≤ a) → st'.memory a = st.memory a

/-- The state is unchanged EXCEPT for the memory high-water mark `activeWords`. This is what a
    body whose only memory operation is `mload` leaves behind: `mload` returns
    `touchMemory st p 32` (EVMExec.lean:750), and `touchMemory` (:366) rewrites `activeWords` and
    nothing else. `st' = st` is FALSE for such a body as soon as it reads above the mark (e.g.
    from `activeWords = 0`). The same idiom as `EntryFrame.shape` (`{ … with activeWords := aw }`,
    Statements.lean:252). -/
def SameUpToActive (st st' : EvmState) : Prop := ∃ aw, st' = { st with activeWords := aw }

/-- What `SameUpToActive` gives a caller that only reads memory, the frame and the halt record.
    PROVED. -/
theorem SameUpToActive.frame {st st' : EvmState} (h : SameUpToActive st st') :
    st'.memory = st.memory ∧ st'.env = st.env ∧ st'.halted = st.halted := by
  obtain ⟨aw, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-- The single function body an emitter prints, constants inlined (a helper's code). -/
def helperBody (consts : Inline.Consts) (emit : Block EVM.Op) : Block EVM.Op :=
  match Inline.inlineContractConstants consts emit with
  | [Stmt.funDef _ _ _ body] => body
  | _ => []

/-! ## 2. PREMISE GAPS (typechecked; NEVER a hypothesis of a row)

  Each `PG_*` is the exact fact a generic row needs and `R.Valid` does not supply. [V3] = supplied
  by the reconciled `ValidV3` (RECON.1: `programOk` with `constsCoherent`, `noShadow`,
  `hasMultiPointSet`, the exit scan; `PayloadAgrees`). [LEMMA] = a lemma about the generator that
  nobody owns yet. [HEADLINE] = a hypothesis of `LoweringEquivalenceV3`, not of validity. -/

/-- PREMISE GAP PG-NOSHADOW [V3: `noShadowB`, StatementsV3.lean:233]. The main-block local `r` is
    bound OUTSIDE every slice (`mainLocals`), and `R.slice q` is inlined on its own with an empty
    shadow list, so a table entry named `r` would be substituted at every `mulmod(…, r)` site.
    `constTableOf` filters `vk` and `success` only (Program.lean:60). -/
def PG_noShadow (R : Render p G₁ G₂ Gₜ) : Prop := R.consts.lookup "r" = none

/-- PREMISE GAP PG-CONSTS-LAG [V3: `constsCoherent`, object/Consts2.lean:155; card OBJ.4]. The table
    binds the six slots `Inv .lagrange` names to the plan view's addresses. `Valid` carries this
    for `VK_MPTR` only (`vkPins`). The seven other names the block reads (`OMEGA_MPTR`,
    `OMEGA_INV_TO_L_MPTR`, `N_INV_MPTR`, `LAGRANGE_DENOMS_MPTR`, `BATCH_INV_SCRATCH_MPTR`,
    `INSTANCE_CPTR`, `X_N_MINUS_1_INV_MPTR`) are not `PlanView.memory` fields `Inv` reads: they need
    `expectedConsts` (Consts2.lean:25) to be stated at all. -/
def PG_constsLag (R : Render p G₁ G₂ Gₜ) : Prop :=
  R.consts.lookup "X_MPTR" = some (ptrAddr R.pv.memory.xMptr) ∧
  R.consts.lookup "X_N_MPTR" = some (ptrAddr R.pv.memory.xNMptr) ∧
  R.consts.lookup "L_LAST_MPTR" = some (ptrAddr R.pv.memory.lLastMptr) ∧
  R.consts.lookup "L_BLIND_MPTR" = some (ptrAddr R.pv.memory.lBlindMptr) ∧
  R.consts.lookup "L_0_MPTR" = some (ptrAddr R.pv.memory.l0Mptr) ∧
  R.consts.lookup "INSTANCE_EVAL_MPTR" = some (ptrAddr R.pv.memory.instanceEvalMptr)

/-- PREMISE GAP PG-CONSTS-TP [V3: `constsCoherent`]. The parser's slots and walk bases. -/
def PG_constsTp (R : Render p G₁ G₂ Gₜ) : Prop :=
  R.consts.lookup "THETA_MPTR" = some (ptrAddr R.pv.memory.thetaMptr) ∧
  R.consts.lookup "BETA_MPTR" = some (ptrAddr R.pv.memory.betaMptr) ∧
  R.consts.lookup "GAMMA_MPTR" = some (ptrAddr R.pv.memory.gammaMptr) ∧
  R.consts.lookup "TRASH_CHALLENGE_MPTR" = some (ptrAddr R.pv.memory.trashChallengeMptr) ∧
  R.consts.lookup "Y_MPTR" = some (ptrAddr R.pv.memory.yMptr) ∧
  R.consts.lookup "X_MPTR" = some (ptrAddr R.pv.memory.xMptr) ∧
  R.consts.lookup "X1_MPTR" = some (ptrAddr R.pv.memory.x1Mptr) ∧
  R.consts.lookup "X2_MPTR" = some (ptrAddr R.pv.memory.x2Mptr) ∧
  R.consts.lookup "X3_MPTR" = some (ptrAddr R.pv.memory.x3Mptr) ∧
  R.consts.lookup "X4_MPTR" = some (ptrAddr R.pv.memory.x4Mptr) ∧
  R.consts.lookup "ADVICE_COMMS_MPTR_BASE" = some (ptrAddr R.pv.memory.adviceCommsMptrBase) ∧
  R.consts.lookup "LOOKUP_M_COMMS_MPTR_BASE" = some (ptrAddr R.pv.memory.lookupMCommsMptrBase) ∧
  R.consts.lookup "PERM_Z_COMMS_MPTR_BASE" = some (ptrAddr R.pv.memory.permZCommsMptrBase) ∧
  R.consts.lookup "LOOKUP_HELPER_COMMS_MPTR_BASE" =
    some (ptrAddr R.pv.memory.lookupHelperCommsMptrBase) ∧
  R.consts.lookup "LOOKUP_Z_COMMS_MPTR_BASE" = some (ptrAddr R.pv.memory.lookupZCommsMptrBase) ∧
  R.consts.lookup "TRASHCAN_COMMS_MPTR_BASE" = some (ptrAddr R.pv.memory.trashcanCommsMptrBase) ∧
  R.consts.lookup "QUOTIENT_LIMB_COMMS_MPTR_BASE" =
    some (ptrAddr R.pv.memory.quotientLimbCommsMptrBase) ∧
  R.consts.lookup "REVERSED_EVALS_MPTR" = some (ptrAddr R.pv.memory.reversedEvalsMptr) ∧
  R.consts.lookup "F_COM_MPTR" = some (ptrAddr R.pv.memory.fComMptr) ∧
  R.consts.lookup "PI_MPTR" = some (ptrAddr R.pv.memory.piMptr) ∧
  R.consts.lookup "Q_EVAL_CPTR_MPTR" = some (ptrAddr R.pv.memory.qEvalCptrMptr) ∧
  R.consts.lookup "PROOF_CPTR" = some R.plan.proofLayout.proofCptr ∧
  R.consts.lookup "NUM_INSTANCE_CPTR" = some R.plan.proofLayout.proofEnd

/-- PREMISE GAP PG-FRMOD [V3: `constsCoherent`]. `Frame.r` says the local `r` holds the TABLE's
    `FR_MODULUS`; `EnvAgrees.modulus` says `p = frModulusConstant`. Nothing says the two agree. -/
def PG_frModulus (R : Render p G₁ G₂ Gₜ) : Prop := R.consts.lookup "FR_MODULUS" = some p

/-- PREMISE GAP PG-PCS-EMIT [LEMMA or V3]. `emitPcsFromPlan` (GenAstDispatch.lean:131) returns `[]`
    when `computationsAst` faults or the plan has no point set. With an empty slice the `.pcs` row
    is FALSE (the exit claims `∃ ms, Decoded R cd ms …`, which the parser never established).
    `SimPins.multiPoint` excludes the empty-plan arm; nothing excludes the fault arms
    (kzg/mod.rs:1677, :1788, :1816 - GenAstPcs.lean:433, :407, :461). -/
def PG_pcsEmits (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ blocks, Midfall.Lowering.GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
      R.pv.truncatedChallenges false = .ok blocks ∧ blocks ≠ []

/-- PREMISE GAP PG-G2SLOTS [V3: `PayloadAgrees.g2Base`, `.negSG2` with `EnvAgrees`]. Already named
    in the tree (Blocks/FinalPairing.lean:234). -/
def PG_g2Slots (R : Render p G₁ G₂ Gₜ) : Prop := Blocks.FinalPairing.fpG2Slots R

/-- PREMISE GAP PG-NEGLAG [to be checked against `WellFormed`]. The block reads `l_blind` from word
    1 and starts the instance walk at word `max 2 numNegLagranges` (GenAst.lean:727-733), so for
    `numNegLagranges < 2` it computes values the Lean verifier does not. `EnvAgrees.negLagranges`
    gives `numNegLagranges = blindingFactors.toOption.getD 0 + 1`, which is 1 when
    `blindingFactors` is an error. -/
def PG_negLagranges (R : Render p G₁ G₂ Gₜ) : Prop := 2 ≤ R.pv.numNegLagranges

/-- PREMISE GAP PG-G1ID [V3 option, `g1IdentityAbove`, StatementsV3.lean:723]. `BaseInv .start`
    needs the `g1_identity` window to be zero; `EntryFrame.zeroAbove` gives zero from `0x80`. -/
def PG_g1IdentityFresh (R : Render p G₁ G₂ Gₜ) : Prop :=
  0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr

/-- The codec override used by the finding below. -/
def breakCompressed (R : Render p G₁ G₂ Gₜ) : Render p G₁ G₂ Gₜ :=
  { R with E := { R.E with g1 := { R.E.g1 with ofCompressed? := fun _ => none } } }

/-- `Valid` does not read the compressed decoder. PROVED. -/
theorem breakCompressed_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    (breakCompressed R).Valid :=
  { hR with slots := { hR.slots with }, supported := { hR.supported with },
            vkPins := { hR.vkPins with }, vkProgressPins := { hR.vkProgressPins with } }

/-- **FINDING (PROVED): `SimPins` IS NOT A CONSEQUENCE OF `Valid`.** If any render is valid, some
    valid render fails `SimPins.compressedEnc`. So a conjunct `SimPins R` in `rows_correct` (as
    PLAN-V3 §5 M5 first specified it) is refutable as soon as `Valid` is inhabited: the codec laws
    are a hypothesis of the headline (`G1CodecHeadlineLaws`), not of validity. THE RECORDED REASON
    `rows_correct` (§1) has no `SimPins` conjunct and no theorem `simPins_of_valid` exists (rule
    W13: a refuted `sorry` must not exist). PREMISE GAP PG-SIMPINS [HEADLINE + V3]. -/
theorem simPins_not_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    ¬ ∀ R' : Render p G₁ G₂ Gₜ, R'.Valid → SimPins R' := by
  intro h
  have hc := (h (breakCompressed R) (breakCompressed_valid R hR)).compressedEnc 1
  cases hc

/-- Where `SimPins` DOES come from after RECON.2 step 4: the four headline laws and one
    `programOk` clause. PROVED. -/
theorem simPins_of_laws (R : Render p G₁ G₂ Gₜ)
    (hlaws : Midfall.LoweringV3.G1CodecHeadlineLaws R.E.g1)
    (hmp : hasMultiPointSet R = true) : SimPins R :=
  ⟨hlaws.compressedEncoderFirst, hlaws.eipRoundtrip, hlaws.toEip_one, hmp⟩

/-! ## 3. HLP.1, generic: the scope of every render defines the helpers the emitter prints -/

section Helpers

variable {c : ExternalCalls} {g : ExternalGas}

/-- **THE GENERIC FORM OF A HELPER SUMMARY'S FIRST HALF.** The block scope of render `R` resolves
    `name` to the declaration that `emit` prints, constants inlined, and the scope visible from
    inside it is the same block scope (so a helper calling `fail` resolves it too). -/
def HelperIs (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) (name : String)
    (emit : Block EVM.Op) : Prop :=
  ∃ ps rs body,
    Inline.inlineContractConstants R.consts emit = [Stmt.funDef name ps rs body] ∧
    lookupFun (R.scope c g) name =
      some (({ params := ps, rets := rs, body := body } : FDecl (Bridge.Dialect c g)),
        R.scope c g)

/-- `fail`, for every render. PROVED (`fail_lookup`, Blocks/TraceReturn.lean:405). -/
theorem fail_is (R : Render p G₁ G₂ Gₜ) : HelperIs R c g "fail" GenAst.emitFail :=
  ⟨_, _, _, rfl, Blocks.TraceReturn.fail_lookup R⟩

/-- `batch_invert`, for every render (emitter: GenAst.lean:465-549; the seventh of eight
    definitions, so `lookupFun` skips six). PROVED by kernel reduction, with NO premise: the helpers
    that precede it bind only names its own body re-binds before use, so the body inlined inside
    the helper block IS the body inlined on its own (`helperBody`). -/
theorem batch_invert_is (R : Render p G₁ G₂ Gₜ) :
    HelperIs R c g "batch_invert" GenAst.emitBatchInvertAt := by
  refine ⟨["success", "mptr_start", "mptr_end", "scratch_mptr", "r"],
    ["ret", "precompile_failed"], helperBody R.consts GenAst.emitBatchInvertAt, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl

/-- The six other helpers, same shape. PROVED by kernel reduction. -/
theorem helpers_are (R : Render p G₁ G₂ Gₜ) :
    HelperIs R c g "scalar_inv" (GenAst.emitScalarInvAt R.pv) ∧
    HelperIs R c g "transcript_init" GenAst.emitTranscriptInit ∧
    HelperIs R c g "common_word" GenAst.emitCommonWord ∧
    HelperIs R c g "common_uncompressed_g1" GenAst.emitCommonUncompressedG1 ∧
    HelperIs R c g "squeeze_to" GenAst.emitSqueezeTo ∧
    HelperIs R c g "ec_pairing" (GenAst.emitEcPairingAt R.pv) := by
  refine ⟨⟨["x"], ["inv"], helperBody R.consts (GenAst.emitScalarInvAt R.pv), ?_, ?_⟩,
    ⟨[], ["buf_len"], helperBody R.consts GenAst.emitTranscriptInit, ?_, ?_⟩,
    ⟨["buf_len", "word"], ["ret"], helperBody R.consts GenAst.emitCommonWord, ?_, ?_⟩,
    ⟨["buf_len", "cptr"], ["ret"], helperBody R.consts GenAst.emitCommonUncompressedG1, ?_, ?_⟩,
    ⟨["buf_len", "mptr"], ["ret"], helperBody R.consts GenAst.emitSqueezeTo, ?_, ?_⟩,
    ⟨["success", "lhs_mptr", "rhs_mptr"], ["ret"],
      helperBody R.consts (GenAst.emitEcPairingAt R.pv), ?_, ?_⟩⟩ <;> kernel_rfl

/-- What `batch_invert(success, a, e, s, r)` leaves behind, at word level. `ret ≠ 0` means every
    word of `[a, e)` was canonical and non-zero and now holds its inverse modulo `r`. -/
def BatchInvertPost (st : EvmState) (succ : U256) (a e s : Nat) (rw : U256)
    (V' : VEnv (Bridge.Dialect c g)) (st' : EvmState) : Prop :=
  ∃ ret pf, VEnv.get V' "ret" = some ret ∧ VEnv.get V' "precompile_failed" = some pf ∧
    st'.env = st.env ∧ st'.halted = st.halted ∧
    (∀ x, (x < a ∨ e ≤ x) → (x < s ∨ s + (e - a) + 0xc0 ≤ x) → st'.memory x = st.memory x) ∧
    (succ = 0 → ret = 0 ∧ pf = 0 ∧ st'.memory = st.memory) ∧
    (pf ≠ 0 → ret = 0) ∧
    (ret ≠ 0 → pf = 0 ∧ ∀ i, a + 32 * i < e →
      (loadWord st.memory (a + 32 * i)).toNat < rw.toNat ∧
      loadWord st.memory (a + 32 * i) ≠ 0 ∧
      (loadWord st'.memory (a + 32 * i)).toNat < rw.toNat ∧
      wMulmod (loadWord st'.memory (a + 32 * i)) (loadWord st.memory (a + 32 * i)) rw = 1)

/-- **THE `batch_invert` SUMMARY (all runs), FOR EVERY TABLE.** Under precompiles that may fail but
    never lie, every run of the body from the callee's entry environment ends normally or by
    `leave` in `BatchInvertPost`; it never halts. LEAF HLP.1.b (parent of HLP.1.c-e). The modulus
    is prime because the inverse comes from modexp with exponent `r - 2`. -/
theorem batch_invert_summary (consts : Inline.Consts) (product : PairingProduct) (g : ExternalGas)
    (funs : FunEnv (Bridge.Dialect (permissive (callsOf product)) g))
    (gas : Nat) (hgas : consts.lookup "MODEXP_GAS" = some gas)
    (succ rw : U256) (a e s : Nat) (hrw : Nat.Prime rw.toNat)
    (hae : a ≤ e) (hal : (e - a) % 32 = 0) (he : e < 2 ^ 256) (hs : s + (e - a) + 0xc0 < 2 ^ 256)
    (hdisj : e ≤ s ∨ s + (e - a) + 0xc0 ≤ a) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g) funs
      (helperBody consts GenAst.emitBatchInvertAt)
      (fun V _ => V = [("success", succ), ("mptr_start", BitVec.ofNat 256 a),
          ("mptr_end", BitVec.ofNat 256 e), ("scratch_mptr", BitVec.ofNat 256 s), ("r", rw),
          ("ret", 0), ("precompile_failed", 0)])
      (fun _ st V' st' o => (o = .normal ∨ o = .leave) ∧
        BatchInvertPost (c := permissive (callsOf product)) (g := g) st succ a e s rw V' st') := by
  sorry

/-- The forward pass (statement 10 of the body, GenAst.lean:499-505): a loop whose bound is the
    batch length. Invariant after `j` iterations: `gp` is the product of words `0..j` modulo `r`,
    every word read was canonical, scratch words `0..j-1` hold the prefix products, the batch is
    untouched. LEAF HLP.1.c (uses the loop rule, GEN.3). -/
theorem bi_forward_loop (consts : Inline.Consts) {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (rw : U256) (a e s : Nat)
    (hae : a + 64 ≤ e) (hal : (e - a) % 32 = 0) (he : e < 2 ^ 256) (hs : s + (e - a) < 2 ^ 256)
    (hdisj : e ≤ s ∨ s + (e - a) ≤ a) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (seg (helperBody consts GenAst.emitBatchInvertAt) 10 1)
      (fun V st => VEnv.get V "mptr" = some (BitVec.ofNat 256 (a + 32)) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 e) ∧
        VEnv.get V "gp_mptr" = some (BitVec.ofNat 256 s) ∧
        VEnv.get V "gp" = some (loadWord st.memory a) ∧ VEnv.get V "r" = some rw ∧
        (VEnv.get V "ret").isSome)
      (fun _ st V' st' o =>
        (o = .leave ∧ VEnv.get V' "ret" = some 0) ∨
        (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          MemSameOutside st st' s (e - a - 64) ∧
          VEnv.get V' "mptr" = some (BitVec.ofNat 256 (e - 32)) ∧
          VEnv.get V' "gp_mptr" = some (BitVec.ofNat 256 (s + (e - a - 64))) ∧
          (∀ i, a + 32 * i + 32 < e → (loadWord st.memory (a + 32 * i)).toNat < rw.toNat) ∧
          ∃ P : Nat → U256, P 0 = loadWord st.memory a ∧
            (∀ i, a + 32 * (i + 1) + 32 < e →
              P (i + 1) = wMulmod (P i) (loadWord st.memory (a + 32 * (i + 1))) rw ∧
              loadWord st'.memory (s + 32 * i) = P (i + 1)) ∧
            VEnv.get V' "gp" = some (P ((e - a) / 32 - 2)))) := by
  sorry

end Helpers

/-! ## 4. The prefix (SIM.6)

  Emitted code: `abiGuardBlock m` (Program.lean:66), `wrapperLocals` (:105), `mainGuardBlock` (:80),
  the eight hoisted helpers (`emitHelpers`, GenAst.lean:579), `mainLocals` (:88). Fixed text; five
  model numerals; no loop, no list, no call that returns. The rows `prefix_sim`, `prefix_prog` are
  `SoundnessV3`'s (:772, :1170) and already take every `R`.

  WAITS FOR: PG-NOSHADOW, PG-FRMOD, PG-G1ID, the two table names `NUM_INSTANCE_CPTR` and
  `TRANSCRIPT_MPTR` of PG-CONSTS-TP, and RECON.2's `Frame.cdSize`. -/

/-- The model's two shape flags under `Valid` (`separateVk`, `embeddedQuotient`), so that
    `wrapperLocals` is the single `let vk`. LEAF SIM.6.a - a lemma about
    `generateVerifierFromPlan` (`Valid.model`), no semantics. -/
theorem model_flags_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    R.model.embeddedVk.isNone = true ∧ R.model.quotientExternal.isSome = false := by
  sorry

/-- The static half of `abiHeadOk` (SIM.6's stop condition, now a card). LEAF SIM.6.b - a lemma
    about `ProofCalldataLayout.fromProtocol` (`Valid.layout`), no semantics. -/
theorem layout_static_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    R.plan.proofLayout.proofCptr = abiVerifyProofProofCptr ∧
    R.plan.proofLayout.proofEnd = R.plan.proofLayout.proofCptr + R.plan.proofLayout.proofLen := by
  sorry

/-- The ABI guard, all runs: it reverts, or changes nothing and the two head words are the ones
    `decodeCalldata` checks. LEAF SIM.6.c. -/
theorem abi_guard_sem (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) {c : ExternalCalls}
    {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g)) (cd : Bytes)
    (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      (Inline.inlineContractConstants R.consts (abiGuardBlock R.model))
      (fun _ st => st.env.calldata = cd.data.toList ∧ st.halted = none)
      (fun V st V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ V' = V ∧ st' = st ∧ abiHeadOk R.plan.proofLayout cd = true)) := by
  sorry

/-- A list of function definitions executes as a no-op. LEAF SIM.6.d (generic in the dialect). -/
theorem funDefs_noop {D : YulSemantics.Dialect} [DecidableEq D.Value] (funs : FunEnv D)
    (b : Block D.Op) (hb : ∀ s ∈ b, ∃ n ps rs body, s = Stmt.funDef n ps rs body)
    (V : VEnv D) (st : D.State) (V' : VEnv D) (st' : D.State) (o : Outcome)
    (h : ExecStmts D funs V st b V' st' o) : V' = V ∧ st' = st ∧ o = .normal := by
  sorry

/-- **THE HELPER BLOCK OF EVERY RENDER, AS A LIST.** Eight definitions, in the template's order,
    each with the body its own emitter prints, inlined on its own. PROVED by kernel reduction. -/
theorem helpers_eq (R : Render p G₁ G₂ Gₜ) :
    R.helpers =
      [Stmt.funDef "fail" ["sel"] [] (helperBody R.consts GenAst.emitFail),
       Stmt.funDef "scalar_inv" ["x"] ["inv"] (helperBody R.consts (GenAst.emitScalarInvAt R.pv)),
       Stmt.funDef "transcript_init" [] ["buf_len"] (helperBody R.consts GenAst.emitTranscriptInit),
       Stmt.funDef "common_word" ["buf_len", "word"] ["ret"]
         (helperBody R.consts GenAst.emitCommonWord),
       Stmt.funDef "common_uncompressed_g1" ["buf_len", "cptr"] ["ret"]
         (helperBody R.consts GenAst.emitCommonUncompressedG1),
       Stmt.funDef "squeeze_to" ["buf_len", "mptr"] ["ret"]
         (helperBody R.consts GenAst.emitSqueezeTo),
       Stmt.funDef "batch_invert" ["success", "mptr_start", "mptr_end", "scratch_mptr", "r"]
         ["ret", "precompile_failed"] (helperBody R.consts GenAst.emitBatchInvertAt),
       Stmt.funDef "ec_pairing" ["success", "lhs_mptr", "rhs_mptr"] ["ret"]
         (helperBody R.consts (GenAst.emitEcPairingAt R.pv))] := by
  kernel_rfl

/-- The hoisted helper block of every render is function definitions only. PROVED. -/
theorem helpers_funDefs (R : Render p G₁ G₂ Gₜ) :
    ∀ s ∈ R.helpers, ∃ n ps rs body, s = Stmt.funDef n ps rs body := by
  intro s hs
  rw [helpers_eq] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl⟩

/-! ## 5. Lagrange (T3.9)

  Emitter: `emitLagrangeAt k numInstances numNegLagranges` (GenAst.lean:681-761). Fixed text with
  four layout numerals; FIVE loops with symbolic bounds (`k`; `n + m` twice; `m - 2`; `n`); one
  call of `batch_invert` (two more loops, one demonic `staticcall`); two `fail` sites.

  WAITS FOR: PG-NOSHADOW, PG-CONSTS-LAG, PG-FRMOD, PG-NEGLAG. -/

/-- The slice is the inlined emitter output. PROVED. -/
theorem lag_slice (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.lagrange = Inline.inlineContractConstants R.consts
      (GenAst.emitLagrangeAt R.pv.k R.pv.numInstances R.pv.numNegLagranges) := rfl

/-- The 28 statements of the block's inner scope, constants inlined. -/
def lagInner (consts : Inline.Consts) (k n m : Nat) : Block EVM.Op :=
  match Inline.inlineContractConstants consts (GenAst.emitLagrangeAt k n m) with
  | [_, Stmt.block body, _] => body
  | _ => []

/-- The inner scope has 28 statements at every table and every layout. PROVED by kernel
    evaluation (`kernel_rfl`, no axiom): the inliner reduces on a symbolic table, as
    `vk_slice_raw` showed for vkLoading. Elaborator `rfl` exceeds the default heartbeats here. -/
theorem lagInner_length (consts : Inline.Consts) (k n m : Nat) :
    (lagInner consts k n m).length = 28 := by kernel_rfl

/-- **THE CARD'S FIRST STEP, DONE ONCE AS EVIDENCE.** Statement 3 of the inner scope, at EVERY
    table and layout, is this loop; the only site left for the table is `r`. PROVED by kernel
    reduction. -/
theorem lag_sq_loop_form (consts : Inline.Consts) (k n m : Nat) :
    seg (lagInner consts k n m) 3 1 =
      [GenAst.yfor [GenAst.ylet "idx" (GenAst.ylit 0)]
        (GenAst.yop EVM.Op.lt [GenAst.yvar "idx", GenAst.yvar "k"])
        [GenAst.yset "idx" (GenAst.yop EVM.Op.add [GenAst.yvar "idx", GenAst.ylit 1])]
        [GenAst.yset "x_n" (GenAst.yop EVM.Op.mulmod
          [GenAst.yvar "x_n", GenAst.yvar "x_n", Blocks.VkLoading.vkSite "r" consts])]] := by
  kernel_rfl

/-- **LOOP 1** (statement 3, GenAst.lean:692-694): `k` squarings. Bound = `k`. LEAF T3.9.a. -/
theorem lag_sq_loop {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (consts : Inline.Consts) (hr : consts.lookup "r" = none) (k n m : Nat) (hk : k < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 3 1)
      (fun V _ => VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧ (VEnv.get V "x_n").isSome ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        ∃ x rw, VEnv.get V "x_n" = some x ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "x_n" (wPow2 rw k x)) := by
  sorry

/-- **LOOP 2** (statement 7, GenAst.lean:700-705): the denominators `x - ω_i`. Bound = `n + m`.
    LEAF T3.9.b. -/
theorem lag_denoms_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aL : Nat)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some aL) (hLb : aL < 2 ^ 256)
    (D : Nat) (hD : D + 32 * (n + m) < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 7 1)
      (fun V _ => VEnv.get V "mptr" = some (BitVec.ofNat 256 D) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (VEnv.get V "x").isSome ∧ (VEnv.get V "omega").isSome ∧ (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧
        ∃ x om rw, VEnv.get V "x" = some x ∧ VEnv.get V "omega" = some om ∧
          VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
          (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
            wAddmod x (rw - omegaPows rw om (loadWord st.memory aL) i) rw) ∧
          MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
          st'.halted = st.halted) := by
  sorry

/-- **LOOP 3** (statement 13, GenAst.lean:718-725): each inverse becomes `L_i(x)`. Bound = `n + m`.
    LEAF T3.9.c. -/
theorem lag_second_pass_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aL : Nat)
    (hL : consts.lookup "OMEGA_INV_TO_L_MPTR" = some aL) (hLb : aL < 2 ^ 256)
    (D : Nat) (hD : D + 32 * (n + m) < 2 ^ 256) (hLD : aL + 32 ≤ D ∨ D + 32 * (n + m) ≤ aL) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 13 1)
      (fun V _ => VEnv.get V "mptr" = some (BitVec.ofNat 256 D) ∧
        VEnv.get V "mptr_end" = some (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
        (VEnv.get V "l_i_common").isSome ∧ (VEnv.get V "omega").isSome ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧
        ∃ lc om rw, VEnv.get V "l_i_common" = some lc ∧ VEnv.get V "omega" = some om ∧
          VEnv.get V "r" = some rw ∧
          V' = VEnv.set V "mptr" (BitVec.ofNat 256 (D + 32 * (n + m))) ∧
          (∀ i, i < n + m → loadWord st'.memory (D + 32 * i) =
            wMulmod lc (wMulmod (loadWord st.memory (D + 32 * i))
              (omegaPows rw om (loadWord st.memory aL) i) rw) rw) ∧
          MemSameOutside st st' D (32 * (n + m)) ∧ st'.env = st.env ∧
          st'.halted = st.halted) := by
  sorry

/-- The running sum `acc + Σ_{i < j} f i` modulo `r`, as `addmod` folds it. -/
def wSum (r : U256) (f : Nat → U256) : Nat → U256 → U256
  | 0, acc => acc
  | j + 1, acc => wAddmod (wSum r f j acc) (f j) r

/-- **LOOP 4** (statement 16, GenAst.lean:729-733): `l_blind`. Bound = `m - 2` (zero iterations
    when `m ≤ 2`; see PG-NEGLAG). LEAF T3.9.d. The body executes `mload(l_i_cptr)`, so the state
    is preserved only up to `activeWords` (`SameUpToActive`; `st' = st` is false for `m ≥ 3`). -/
theorem lag_lblind_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m D : Nat)
    (hDn : consts.lookup "LAGRANGE_DENOMS_MPTR" = some D) (hm : 2 ≤ m)
    (hD : D + 32 * m < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 16 1)
      (fun V _ => VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 (D + 64)) ∧
        (VEnv.get V "l_blind").isSome ∧ (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ SameUpToActive st st' ∧
        ∃ lb rw, VEnv.get V "l_blind" = some lb ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "l_blind"
              (wSum rw (fun i => loadWord st.memory (D + 64 + 32 * i)) (m - 2) lb))
            "l_i_cptr" (BitVec.ofNat 256 (D + 32 * m))) := by
  sorry

/-- **LOOP 5** (statement 18, GenAst.lean:738-746): the public-instance polynomial at `x`.
    Bound = `n`; two cursors advance together. LEAF T3.9.e. The body executes `mload(l_i_cptr)`
    (`calldataload` does not touch the state, EVMExec.lean:791), so the state is preserved only up
    to `activeWords` (`SameUpToActive`; `st' = st` is false for `n ≥ 1`). -/
theorem lag_instance_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k n m aI Lc : Nat) (cd : Bytes)
    (hI : consts.lookup "INSTANCE_CPTR" = some aI)
    (hIb : aI + 32 * n < 2 ^ 256) (hLb : Lc + 32 * n < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (lagInner consts k n m) 18 1)
      (fun V st => st.env.calldata = cd.data.toList ∧
        VEnv.get V "l_i_cptr" = some (BitVec.ofNat 256 Lc) ∧
        VEnv.get V "instance_eval" = some 0 ∧ (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ SameUpToActive st st' ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "instance_eval"
              (wSum rw (fun j => wMulmod (loadWord st.memory (Lc + 32 * j))
                (cdWord cd (aI + 32 * j)) rw) n 0))
            "l_i_cptr" (BitVec.ofNat 256 (Lc + 32 * n))) := by
  sorry

/-- The five words the block persists, as a relation on words (the SEM/ALG interface). `den i` is
    the `i`-th denominator, `inv i` its inverse, `L i` the Lagrange value at word `i`. -/
structure LagWords where
  xn : U256
  lLast : U256
  lBlind : U256
  l0 : U256
  instEval : U256

/-- What the block computes from `(r, x, ω, ω⁻ᴸ, n⁻¹)` and the instance words. -/
def LagRel (rw x om w0 nInv : U256) (k n m : Nat) (inst : Nat → U256) (W : LagWords) : Prop :=
  W.xn = wPow2 rw k x ∧
  ∃ inv : Nat → U256,
    (∀ i, i < n + m →
      wMulmod (inv i) (wAddmod x (rw - omegaPows rw om w0 i) rw) rw = 1 ∧
      (inv i).toNat < rw.toNat) ∧
    let L : Nat → U256 := fun i =>
      wMulmod (wMulmod (wAddmod W.xn (rw - 1) rw) nInv rw)
        (wMulmod (inv i) (omegaPows rw om w0 i) rw) rw
    W.lLast = L 0 ∧ W.l0 = L m ∧
    W.lBlind = wSum rw (fun i => L (2 + i)) (m - 2) (L 1) ∧
    W.instEval = wSum rw (fun j => wMulmod (L (m + j)) (inst j) rw) n 0

/-- **THE ALG LEAF: the word relation is the Lean verifier's Lagrange step.** No Yul. `EnvAgrees`
    supplies `n = 2^k`, the barycentric weight, `ω⁻¹ω = 1` and `numNegLagranges`. LEAF T3.9.g.
    WAITS FOR PG-NEGLAG (`2 ≤ numNegLagranges`) - without it the conclusion is false. -/
theorem lag_agrees (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hm : 2 ≤ R.pv.numNegLagranges)
    (s2 : SnapAlgebra p G₁) (l : SnapLagrange p G₁)
    (hl : snapshotLagrangeStep (G₁ := G₁) R.vk s2 = .ok l)
    (hxn : s2.alg.xn = s2.alg.x ^ (2 ^ R.pv.k))
    (inst : Array (Fr p)) (W : LagWords)
    (hW : LagRel (BitVec.ofNat 256 p) (frWord s2.alg.x) (frWord R.vk.domain.omega)
      (frWord (R.vk.domain.omegaInv ^ (R.pv.numNegLagranges - 1)))
      (frWord (((2 ^ R.vk.domain.k : ℕ) : Fr p)⁻¹)) R.pv.k R.pv.numInstances
      R.pv.numNegLagranges (fun j => frWord (inst.getD j 0)) W) :
    W.xn = frWord s2.alg.xn ∧ W.lLast = frWord l.lagrange.lLast ∧
    W.lBlind = frWord l.lagrange.lBlind ∧ W.l0 = frWord l.lagrange.l0 ∧
    ∀ e, l.instanceEval = some e → W.instEval = frWord e := by
  sorry

/-- **THE POISONED HALF.** With `success = 0` the call returns `(0, 0)` and the last statement
    reverts with `ERR_PROOF_REJECTED`: every run reverts. LEAF T3.9.h. -/
theorem lag_poison (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
      (R.scope (permissive (callsOf product)) g) (R.slice Partial.lagrange)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ _ st' o => o = .halt ∧ Reverted st') := by
  sorry

/-- **THE GENERIC ROW.** LEAF T3.9 (glue: loops a-e, HLP.1.b, `lag_agrees`, `lag_poison`, the frame
    card T3.9.f). -/
theorem lag_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.lagrange H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- **THE GENERIC PROGRESS ROW** - the only reader of `CompleteSide` (`xⁿ ≠ 1`, `x ≠ ωⁱ`). -/
theorem lag_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.lagrange H vkAddr product cd := by
  sorry

/-! ## 6. TranscriptParser (ROW.TP)

  Emitter: `emitTranscriptParserAt` (GenAst.lean:1073-1178). Fixed head and tail; TWO list
  inductions (`userPhases`, `L.lookups`), a third inside each phase (`List.range numChallenges`);
  loops with symbolic bounds: the instance run (`numInstances`), up to six G1 walks
  (`byteLen / 128` each - one shape, `g1WalkLoop`, :1022), the evals spill (`evals.byteLen / 32`)
  and the q_evals run (`qEvals.byteLen / 32`); four optional sections; four loop-free helpers.

  WAITS FOR: PG-CONSTS-TP, PG-FRMOD, PG-NOSHADOW, PG-PARSER (below). -/

/-- The parser's schedule as data: what it absorbs, copies and squeezes, in order. The emitter is
    a fold of this list; the SEM children prove the fold, the ALG child relates the list to the
    Lean transcript. -/
inductive TEv
  /-- `common_word(buf, w)` of a word that is not calldata (the VK digest, the instance count). -/
  | word
  /-- The committed instance: 128 zero bytes. -/
  | zeros
  /-- One public input, range-folded into `success`. -/
  | inst
  /-- One 128-byte frame absorbed and copied to the walk or slot `dst`. -/
  | g1 (dst : String)
  /-- One scalar, range-checked, absorbed, and spilled to the evals window when `spill`. -/
  | fr (spill : Bool)
  /-- `squeeze_to(buf, add(slot, off))`. -/
  | squeeze (slot : String) (off : Nat)
  /-- The 128-bit mask on `X3_MPTR`. -/
  | mask
  /-- `mstore(Q_EVAL_CPTR_MPTR, proof_cptr)`. -/
  | saveCptr
  deriving DecidableEq, Repr

/-- One walk loop: a frame per 128 bytes. -/
def tpWalk (dst : String) (bytes : Nat) : List TEv := List.replicate (bytes / 128) (TEv.g1 dst)

/-- The schedule `emitTranscriptParserAt` prints, argument for argument. -/
def tpEvents (numInstances : Nat) (userPhases : List UserPhase)
    (numLookups numPermutationZs lookupHPlusAcc numTrashcans : Nat)
    (truncatedChallenges : Bool) (L : ProofCalldataLayout) : List TEv :=
  [TEv.word, TEv.zeros, TEv.word] ++ List.replicate numInstances TEv.inst ++
  (userPhases.flatMap fun ph => tpWalk "advice_walk" ph.adviceBytes ++
    (List.range ph.numChallenges).map fun j =>
      TEv.squeeze "CHALLENGE_MPTR" ((ph.challengeOffset + j) * 32)) ++
  [TEv.squeeze "THETA_MPTR" 0] ++
  (if numLookups != 0 then tpWalk "lookup_m_walk" L.lookupMultiplicities.byteLen else []) ++
  [TEv.squeeze "BETA_MPTR" 0, TEv.squeeze "GAMMA_MPTR" 0] ++
  (if numPermutationZs != 0 then tpWalk "perm_z_walk" L.permutationProducts.byteLen else []) ++
  (if lookupHPlusAcc != 0 then
    L.lookups.flatMap fun lk =>
      tpWalk "lookup_helper_walk" lk.helpers.byteLen ++ [TEv.g1 "lookup_z_walk"] else []) ++
  [TEv.squeeze "TRASH_CHALLENGE_MPTR" 0] ++
  (if numTrashcans != 0 then tpWalk "trashcan_walk" L.trash.byteLen else []) ++
  [TEv.squeeze "Y_MPTR" 0] ++ tpWalk "quotient_walk" L.quotientLimbs.byteLen ++
  [TEv.squeeze "X_MPTR" 0] ++ List.replicate (L.evals.byteLen / 32) (TEv.fr true) ++
  [TEv.squeeze "X1_MPTR" 0, TEv.squeeze "X2_MPTR" 0, TEv.g1 "F_COM_MPTR",
   TEv.squeeze "X3_MPTR" 0] ++
  (if truncatedChallenges then [TEv.mask] else []) ++ [TEv.saveCptr] ++
  List.replicate (L.qEvals.byteLen / 32) (TEv.fr false) ++
  [TEv.squeeze "X4_MPTR" 0, TEv.g1 "PI_MPTR"]

/-- The calldata slot an event reads, if any. -/
def TEv.slot? : TEv → Option WireSlot
  | .g1 _ => some WireSlot.g1
  | .fr _ => some WireSlot.fr
  | _ => none

/-- The schedule of a render. -/
def _root_.Midfall.LoweringV2.Render.tpEvents (R : Render p G₁ G₂ Gₜ) : List TEv :=
  Midfall.LoweringV2.V3.Gen.tpEvents R.pv.numInstances R.pv.userPhases R.pv.numLookups R.pv.numPermutationZs
    R.pv.lookupHPlusAcc R.pv.numTrashcans R.pv.truncatedChallenges R.pv.proofLayout

/-- **THE READ SCHEDULE IS THE LAYOUT'S SLOT LIST.** The parser reads, in order, exactly the slots
    `rawSlots` walks. This is where the emitter's inputs (`parserFactsOfPlan` of the MODEL) meet
    `decodeCalldata`'s (the PLAN's layout). LEAF ROW.TP.6 (ALG, list induction, no Yul).
    PREMISE GAP PG-PARSER [LEMMA about `generateVerifierFromPlan`, or V3]: nothing in `Valid`
    relates `R.pv.userPhases`, `.lookupHPlusAcc`, the three counts and the section guards to
    `R.plan.proofLayout`. Witness and falsifier: `GeneratorRowsWitness.lean`. -/
theorem tp_events_slots (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) :
    R.tpEvents.filterMap TEv.slot? =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots := by
  sorry

/-- The inliner distributes over a concatenation, threading the left block's binders: the fact
    every list-induction child needs before it can speak about one group of statements. LEAF
    GEN.4 (replaces the sorried `inline_append`, ProgramLemmas.lean:27, whose side condition is
    then a corollary). -/
theorem inlineScan_append (fuel : Nat) (consts : Inline.Consts) (sh : List String)
    (a b : List (Stmt EVM.Op)) :
    (Inline.inlineScan (fuel + 1) consts sh (a ++ b)).blks =
      (Inline.inlineScan (fuel + 1) consts sh a).blks ++
        (Inline.inlineScan (fuel + 1) consts (sh ++ a.flatMap Inline.boundOf) b).blks := by
  sorry

/-- A walk loop is constant-free where its three cursors are bound: the inliner returns it
    unchanged. So a walk is FIXED TEXT plus one numeral, at every table. LEAF ROW.TP.1. -/
theorem inline_g1WalkLoop (fuel : Nat) (consts : Inline.Consts) (sh : List String)
    (walk : String) (bytes : Nat) (hw : Inline.shadowed sh walk = true)
    (hp : Inline.shadowed sh "proof_cptr" = true) (hb : Inline.shadowed sh "buf_len" = true) :
    (Inline.inlineScan (fuel + 2) consts sh [GenAst.g1WalkLoop walk bytes]).blks =
      [GenAst.g1WalkLoop walk bytes] := by
  sorry

/-- **THE WALK LOOP (all runs), ONE LEMMA FOR SIX SECTIONS.** Bound = `j`, the section's frame
    count. Every run reverts (a frame fails the range check), or ends normally having absorbed the
    `j` frames, copied them to the walk window, and advanced the three cursors; every frame passed
    `g1WordsOk`. LEAF ROW.TP.2 (loop rule GEN.3 + the `common_uncompressed_g1` summary). -/
theorem g1walk_loop_sem (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas}
    (cd : Bytes) (walk : String) (hwalk : walk ≠ "proof_cptr" ∧ walk ≠ "buf_len" ∧ walk ≠ "end")
    (j a w b : Nat) (ha : a + 128 * j ≤ cd.size) (hcd : cd.size < 2 ^ 256)
    (hw : w + 128 * j < 2 ^ 256) (hb : b + 128 * j < 2 ^ 256)
    (hdisj : w + 128 * j ≤ b ∨ b + 128 * j ≤ w) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) [GenAst.g1WalkLoop walk (128 * j)]
      (fun V st => st.env.calldata = cd.data.toList ∧
        VEnv.get V "proof_cptr" = some (BitVec.ofNat 256 a) ∧
        VEnv.get V walk = some (BitVec.ofNat 256 w) ∧
        VEnv.get V "buf_len" = some (BitVec.ofNat 256 b))
      (fun V st V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
          V' = VEnv.set (VEnv.set (VEnv.set V "buf_len" (BitVec.ofNat 256 (b + 128 * j)))
            walk (BitVec.ofNat 256 (w + 128 * j))) "proof_cptr" (BitVec.ofNat 256 (a + 128 * j)) ∧
          bytesAt st' w (128 * j) = cdSlice cd a (128 * j) ∧
          bytesAt st' b (128 * j) = cdSlice cd a (128 * j) ∧
          (∀ i, i < j → g1WordsOk cd (a + 128 * i) = true) ∧
          (∀ x, (x < w ∨ w + 128 * j ≤ x) → (x < b ∨ b + 128 * j ≤ x) →
            st'.memory x = st.memory x))) := by
  sorry

/-- The part of `Agree .transcript` that is about squeezed words: for every decoding, the ten
    challenge slots hold the transcript-only run's challenges. -/
def XcriptSlots (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (st : EvmState) : Prop :=
  ∀ ms instW inst, Decoded R cd ms instW inst →
    ∀ x, snapshotXcriptRun R.E H R.vk inst ms R.nSets = .ok x →
      holdsFr st (ptrAddr R.pv.memory.thetaMptr) x.trace.theta = true ∧
      holdsFr st (ptrAddr R.pv.memory.betaMptr) x.trace.beta = true ∧
      holdsFr st (ptrAddr R.pv.memory.gammaMptr) x.trace.gamma = true ∧
      holdsFr st (ptrAddr R.pv.memory.trashChallengeMptr) x.trace.trashChallenge = true ∧
      holdsFr st (ptrAddr R.pv.memory.yMptr) x.trace.y = true ∧
      holdsFr st (ptrAddr R.pv.memory.xMptr) x.alg.x = true ∧
      holdsFr st (ptrAddr R.pv.memory.x1Mptr) x.r.x1 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x2Mptr) x.r.x2 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x3Mptr) x.r.x3 = true ∧
      holdsFr st (ptrAddr R.pv.memory.x4Mptr) x.r.x4 = true

/-- What a normal exit of the parser has established, with NO fact about a decoded point outside
    the `∀ decoding` of `XcriptSlots`. -/
def TpPost (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧
    BaseInv R Checkpoint.transcript V st ∧
    (rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd).isSome = true ∧
    MirrorAt R cd st ∧ XcriptSlots R H cd st

/-- **THE SEM LEAF.** From a staged boundary at `.vk` every run reverts or exits normally in
    `TpPost`. LEAF ROW.TP.7 (glue of ROW.TP.2-5 along `tpEvents`). -/
theorem tp_computes (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hpins : SimPins R) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.transcriptParser)
      (fun V st => StageInv R H vkAddr cd Checkpoint.vk V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ TpPost R H vkAddr cd V' st')) := by
  sorry

/-- **THE ALG LEAF.** `TpPost` is the staged boundary at `.transcript`: `Agree` follows from
    `xcript_total` (the Lean prefix exists), `MirrorAt` with `SimPins.eipRt` (the commitment
    windows hold `toEip` of the decoded points) and `XcriptSlots`. LEAF ROW.TP.8. No Yul. -/
theorem tp_agrees (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (hpins : SimPins R) (H : Hash)
    (vkAddr : U256) (cd : Bytes) {c : ExternalCalls} {g : ExternalGas}
    (V : VEnv (Bridge.Dialect c g)) (st : EvmState) (h : TpPost R H vkAddr cd V st) :
    StageInv R H vkAddr cd Checkpoint.transcript V st := by
  sorry

/-- **THE POISONED HALF.** No statement raises `success`; the last statement reverts on
    `success = 0`. LEAF ROW.TP.9. -/
theorem tp_poison (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.transcriptParser)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ _ st' o => o = .halt ∧ Reverted st') := by
  sorry

/-- **THE GENERIC ROW, PROVED from the three leaves.** -/
theorem tp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (_hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.transcriptParser H vkAddr (permissive (callsOf product)) g cd := by
  refine ⟨?_, ?_⟩
  · intro V st hpre V' st' o hrun
    rcases tp_computes R hR hpins H vkAddr cd _ g V st hpre V' st' o hrun with hrev | ⟨ho, hpost⟩
    · exact Or.inl hrev
    · exact Or.inr (Or.inl ⟨ho, tp_agrees R hR hpins H vkAddr cd V' st' hpost⟩)
  · intro V st hpre V' st' o hrun
    exact Or.inl (tp_poison R hR H vkAddr cd _ g V st hpre V' st' o hrun)

/-- **THE GENERIC PROGRESS ROW.** LEAF ROW.TP.10. -/
theorem tp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.transcriptParser H vkAddr product cd := by
  sorry

/-! ## 7. QuotientLin (ROW.Q)

  AT cf00592 the slice is `emitQuotientLinAt k` only (GenAst.lean:840-864): ten statements, one loop
  with bound `k`. The quotient numerator (6,384 tokens at F1: the QVM interpreter template and six
  families of generated lines) is NOT in the program (`CodegenAgrees` is false; OBJ.2 adds it as a
  PARSE of the rendered text).

  PREMISE GAP PG-Q-OBJECT [GEN work, not a clause]. A parse of rendered text is an opaque function
  of the model: no induction over it exists. For a row at every `R` the region needs AST emitters:
  `emitQuotientHelpersA` (OBJ.14), `emitQuotientNumeratorA` (OBJ.15) and - not carded anywhere -
  AST twins of the six block producers of `compactQuotientComputationBlocks` (`R.qblocks`).
  Until they exist only the linearization scope below can be stated against an emitter.

  Route A (execute one circuit's numerator) is excluded by D-P71. Route B: the interpreter loop
  refines `evalQuotientIdentity` once (`QInterpRefines`), and the builder is correct for every
  plan: `Qvm.lean:631, :698, :713, :768, :995`, `QvmFold.lean:338, :376, :434` come INTO scope. -/

/-- The slice at cf00592. PROVED. -/
theorem qlin_slice (R : Render p G₁ G₂ Gₜ) :
    R.slice Partial.quotientLin =
      Inline.inlineContractConstants R.consts (GenAst.emitQuotientLinAt R.pv.k) := rfl

/-- The ten statements of the linearization scope, constants inlined. -/
def qlinInner (consts : Inline.Consts) (k : Nat) : Block EVM.Op :=
  match Inline.inlineContractConstants consts (GenAst.emitQuotientLinAt k) with
  | [Stmt.block body] => body
  | _ => []

theorem qlinInner_length (consts : Inline.Consts) (k : Nat) :
    (qlinInner consts k).length = 9 := by kernel_rfl

/-- The pair `(x^(2^i - 1), x^(2^i))` after `i` iterations of the split loop. -/
def wSplit (r x : U256) : Nat → U256 × U256
  | 0 => (1, x)
  | i + 1 => (wMulmod (wMulmod (wSplit r x i).1 (wSplit r x i).1 r) x r,
              wMulmod (wSplit r x i).2 (wSplit r x i).2 r)

/-- **THE SPLIT LOOP** (statement 4, GenAst.lean:851-856). Bound = `k`. LEAF ROW.Q.1. -/
theorem qlin_split_loop {c : ExternalCalls} {g : ExternalGas}
    (funs : FunEnv (Bridge.Dialect c g)) (consts : Inline.Consts)
    (hr : consts.lookup "r" = none) (k : Nat) (hk : k < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs (seg (qlinInner consts k) 4 1)
      (fun V _ => VEnv.get V "k" = some (BitVec.ofNat 256 k) ∧
        VEnv.get V "x_pow_2i_minus1" = some 1 ∧
        (VEnv.get V "x").isSome ∧ VEnv.get V "x_pow_2i" = VEnv.get V "x" ∧
        (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ st' = st ∧
        ∃ x rw, VEnv.get V "x" = some x ∧ VEnv.get V "r" = some rw ∧
          V' = VEnv.set (VEnv.set V "x_pow_2i_minus1" (wSplit rw x k).1)
            "x_pow_2i" (wSplit rw x k).2) := by
  sorry

/-- **THE CONTRACT SHAPE OF ROUTE B's ONE-OFF LEMMA.** `interp` is the interpreter loop of the
    numerator block as an emitter will print it (OBJ.15); the definition says what "refines the
    reference VM" means for it: started on a memory whose program window holds `bytes` and whose
    constant window holds `consts`, at an identity segment `[cursor, exprEnd)`, every run reverts
    (`q_program_fail`) or leaves on the VM stack the word the reference interpreter computes, on
    the reference memory `mem` that the Yul memory `Agrees` with. `Agrees` is the frame valuation
    (`QuotientReadModel`'s windows): its statement is card ROW.Q.4. -/
def QInterpRefines {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (interp : Block EVM.Op) (bytes : List Nat) (consts : List Word256)
    (Agrees : EvmState → QuotientRefMemory → Prop)
    (AtSegment : VEnv (Bridge.Dialect c g) → EvmState → Nat → Prop)
    (Top : VEnv (Bridge.Dialect c g) → EvmState → U256 → Prop) : Prop :=
  ∀ (cursor exprEnd : Nat) (mem : QuotientRefMemory),
    StmtsContractAll (D := Bridge.Dialect c g) funs interp
      (fun V st => AtSegment V st cursor ∧ Agrees st mem)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ ∃ v mem',
          Midfall.Generator.evalQuotientIdentity ((bytes.drop cursor).take (exprEnd - cursor))
            consts mem = .ok (v, mem') ∧
          Top V' st' (BitVec.ofNat 256 v) ∧ AtSegment V' st' exprEnd))

/-- **`identityCorrespondence_of_bridge`, CORRECTED** (QvmFold.lean:327 is refuted by the same
    file, :718-749: no hypothesis mentions `Prod.snd`). The missing hypothesis is `hsnd`, the
    frame-valuation agreement. PROVED. -/
theorem identityCorrespondence_of_bridge_fixed (plan : QuotientProgramPlan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) (ρ : Valuation)
    (horder : exprs.size = (globalIdentities plan).length)
    (hvals : vals = (globalIdentities plan).map
              fun id => (evalExprρ ρ id.expr).toOption.getD 0)
    (htags : ∀ i (h : i < (globalIdentities plan).length),
              (exprs[i]?.map Prod.fst) =
                some (match (globalIdentities plan)[i]'h |>.target with
                      | .main => (none : Option Nat)
                      | .selector s => plan.sortedSimple[s]?))
    (hsnd : ∀ i, i < (globalIdentities plan).length →
              exprs[i]?.map Prod.snd = some (qvmToFr (vals[i]?.getD 0))) :
    IdentityCorrespondence plan exprs vals := by
  refine ⟨horder, by rw [hvals, List.length_map], fun i h => ⟨hsnd i h, ?_⟩⟩
  have ht := htags i h
  cases htgt : ((globalIdentities plan)[i]'h).target with
  | main => rw [htgt] at ht; exact ht
  | selector s => rw [htgt] at ht; exact ht

/-- **THE GENERIC ROW** - the only reader of `SoundSide`. -/
theorem q_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (hside : SoundSide R H cd) (g : ExternalGas) :
    BlockSim R Partial.quotientLin H vkAddr (permissive (callsOf product)) g cd := by
  sorry

theorem q_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.quotientLin H vkAddr product cd := by
  sorry

/-! ## 8. PCS (ROW.PCS)

  Emitter: `emitPcsFromPlan` (GenAstDispatch.lean:131) = `computationsAst` flattened
  (GenAstPcs.lean:587-611): block 1 (:131, the rotation walk - two list inductions over rotation
  ranges), block 2 (:163, ONE loop, bound `nbX1Powers - 1`), block 3 per point set (:193, list
  induction over the sets; the rolled arm has ONE loop, bound = commitments in the set), block 4
  (:317, list induction over the reversed sets; each set :254 is straight-line lists over its
  points with one `scalar_inv`), block 5 (:425, `foldlM` over sets × commitments with one pair
  counter; `pcsLinExpansion` :387; one G1MSM `staticcall`), block 6 (:485, fixed text, four
  `staticcall`s).

  WAITS FOR: PG-PCS-EMIT, PG-NOSHADOW, the PCS names of `constsCoherent`. -/

/-- The slice is the flattened blocks when the emitter does not fault. PROVED. -/
theorem pcs_slice_of_ok (R : Render p G₁ G₂ Gₜ) (blocks : List (Block EVM.Op))
    (h : Midfall.Lowering.GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
      R.pv.truncatedChallenges false = .ok blocks) :
    R.slice Partial.pcs = Inline.inlineContractConstants R.consts blocks.flatten := by
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.pcs) = _
  simp only [GenAst.emitPartial, GenAst.emitPcsFromPlan, h]

/-- **FINDING (PROVED): on the fault arm the slice is empty**, so the `.pcs` row needs
    PG-PCS-EMIT. -/
theorem pcs_slice_of_fault (R : Render p G₁ G₂ Gₜ) (f : Midfall.Halo2.Fault)
    (h : Midfall.Lowering.GenAstPcs.computationsAst R.pv.meta_ R.pv.dat R.pv.memory
      R.pv.truncatedChallenges false = .error f) :
    R.slice Partial.pcs = [] := by
  show Inline.inlineContractConstants R.consts (GenAst.emitPartial R.pv Partial.pcs) = _
  simp only [GenAst.emitPartial, GenAst.emitPcsFromPlan, h]
  rfl

/-- The x1 power table, as the loop of block 2 writes it. -/
def wPowers (r x1 : U256) (mask : Bool) : Nat → U256 × U256
  | 0 => (1, 1)
  | i + 1 =>
      let acc := wMulmod (wPowers r x1 mask i).1 x1 r
      (acc, if mask then acc &&& BitVec.ofNat 256 (2 ^ 128 - 1) else acc)

/-- **BLOCK 2** (GenAstPcs.lean:163-176): the only loop of the PCS region outside the rolled arm.
    Bound = `nb - 1`. LEAF ROW.PCS.2. -/
theorem pcs_b2_sem {c : ExternalCalls} {g : ExternalGas} (funs : FunEnv (Bridge.Dialect c g))
    (consts : Inline.Consts) (hr : consts.lookup "r" = none) (nb : Nat) (trunc : Bool)
    (a1 aP : Nat) (h1 : consts.lookup "X1_MPTR" = some a1)
    (hP : consts.lookup "X1_POWERS_MPTR" = some aP) (hnb : aP + 32 * nb < 2 ^ 256)
    (ha1 : a1 + 32 ≤ aP ∨ aP + 32 * nb ≤ a1) (ha1b : a1 < 2 ^ 256) :
    StmtsContractAll (D := Bridge.Dialect c g) funs
      [Stmt.block (Inline.inlineContractConstants consts
        (Midfall.Lowering.GenAstPcs.pcsBlock2Ast nb trunc))]
      (fun V _ => (VEnv.get V "r").isSome)
      (fun V st V' st' o => o = .normal ∧ V' = V ∧ st'.env = st.env ∧ st'.halted = st.halted ∧
        MemSameOutside st st' aP (32 * (max nb 1)) ∧
        ∃ rw, VEnv.get V "r" = some rw ∧
          ∀ i, i < max nb 1 → loadWord st'.memory (aP + 32 * i) =
            (wPowers rw (loadWord st.memory a1) trunc i).2) := by
  sorry

/-- **THE DECODE-EXISTS LEMMA (SIM.12), ALG.** The parser established the raw walk; if every frame
    is a group element the calldata decodes. PCS proves the second hypothesis from G1MSM
    (`Holds.g1Decodes`) and the coverage invariant. LEAF ROW.PCS.9. No Yul. -/
theorem decode_exists (R : Render p G₁ G₂ Gₜ) (cd : Bytes) (raw : List (RawMsg p))
    (instW : Array Word256)
    (hraw : rawDecode (p := p) R.plan.proofLayout R.cfg.numInstances cd = some (raw, instW))
    (hpts : ∀ b, RawMsg.g1 b ∈ raw → (R.E.g1.ofEip? b).isSome = true) :
    ∃ ms instW' inst, Decoded R cd ms instW' inst := by
  sorry

/-- **THE GENERIC ROW.** -/
theorem pcs_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.pcs H vkAddr (permissive (callsOf product)) g cd := by
  sorry

theorem pcs_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.pcs H vkAddr product cd := by
  sorry

/-! ## 9. FinalPairing (ROW.FP)

  Emitter: `emitFinalPairingArms false _` (GenAst.lean:649-654): two statements, fixed text. The
  helper `ec_pairing` (`emitEcPairing`, :265-292): fixed text with four numerals, one `staticcall`,
  two `fail` sites, one `leave`. No loop, no list.

  The tree's `Blocks/FinalPairing.lean` already takes every `R`. Its `ec_pairing_contract` (:314)
  is false as stated (REVIEW-V3 RV-23) and takes `fpG2Slots` as a free premise (PG-G2SLOTS). -/

/-- **THE POISONED HALF, PROVED** from the tree's `fp_stmt_steps` (Blocks/FinalPairing.lean:352,
    a registered sorry). -/
theorem fp_poison (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (H : Hash) (vkAddr : U256)
    (cd : Bytes) (c : ExternalCalls) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice Partial.finalPairing)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (Partial.finalPairing ≠ Partial.traceReturn ∧ o = .normal ∧
          Poisoned R H vkAddr cd V' st')) := by
  intro V st hpre V' st' o hrun
  rcases Blocks.FinalPairing.fp_stmt_steps R hR H vkAddr cd c g V st hpre V' st' o hrun with
      hrev | ⟨ho, hp⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨by decide, ho, hp⟩

/-- **THE `ec_pairing` SUMMARY, RESTATED (ROW.FP step 1).** At ANY call relation that may fail but
    never lies, from `success ∈ {0, 1}` and the two G1 slots readable: every run of the slice
    reverts, or exits normally with `success` equal to the AND of the incoming bit and the
    product's answer on the frame that is IN MEMORY (bytes, not snapshot fields). The frame is
    read off memory so that no base-point pin is needed to STATE it (HLP.1's stop condition).
    LEAF ROW.FP.1. -/
theorem ec_pairing_sem (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (product : PairingProduct)
    (H : Hash) (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    StmtsContractAll (D := Bridge.Dialect (permissive (callsOf product)) g)
      (R.scope (permissive (callsOf product)) g) (R.slice Partial.finalPairing)
      (fun V st => Frame R H vkAddr cd V st ∧ st.halted = none ∧
        VEnv.get V "success" = some (1 : U256))
      (fun _ st V' st' o => (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ Frame R H vkAddr cd V' st' ∧ st'.halted = none ∧
          VEnv.get V' "success" = some (1 : U256) ∧
          product (pairingFrame
            [(bytesAt st (ptrAddr R.pv.memory.pairingRhsMptr) 128,
              vkG2Words R.pv vkG2BaseSlot),
             (bytesAt st (ptrAddr R.pv.memory.pairingLhsMptr) 128,
              vkG2Words R.pv vkNegSG2BaseSlot)]) = true ∧
          (∀ x, (x < R.pv.memory.finalPairingScratchMptr ∨
              R.pv.memory.finalPairingScratchMptr + 0x300 ≤ x) →
            st'.memory x = st.memory x))) := by
  sorry

/-- **THE GENERIC ROW.** LEAF ROW.FP (glue: `ec_pairing_sem`, `fp_pairing_algebra`, `fp_poison`,
    `fp_blockSim_of_blockSound`'s argument). -/
theorem fp_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.finalPairing H vkAddr (permissive (callsOf product)) g cd := by
  sorry

theorem fp_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.finalPairing H vkAddr product cd := by
  sorry

/-! ## 1. `rows_correct`, and what the headline needs beyond it: its own codec laws, nothing else

  (Placed after the rows so that it can cite them.) vkLoading is card GEN.1's; its two rows are
  stated here in the staged form GEN.1 lands. -/

/-- GEN.1's deliverable, soundness half. -/
theorem vk_blockSim (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (g : ExternalGas) :
    BlockSim R Partial.vkLoading H vkAddr (permissive (callsOf product)) g cd := by
  sorry

/-- GEN.1's deliverable, progress half. -/
theorem vk_blockProgS (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product)
    (hcodec : G1CodecLaws R.E.g1) (H : Hash) (vkAddr : U256) (cd : Bytes)
    (hacc : LeanAccepts R H cd) (hcomp : CompleteSide R H cd) :
    BlockProgS R Partial.vkLoading H vkAddr product cd := by
  sorry

/-- **THE SEVEN SIMULATION ROWS OF EVERY VALID RENDER, PROVED from the per-block rows.** -/
theorem sim_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    R.SimContracts product := by
  intro hR hpins hpc H vkAddr cd hside q g
  cases q with
  | vkLoading => exact vk_blockSim R product hR hpins hpc H vkAddr cd g
  | transcriptParser => exact tp_blockSim R product hR hpins hpc H vkAddr cd g
  | lagrange => exact lag_blockSim R product hR hpins hpc H vkAddr cd g
  | quotientLin => exact q_blockSim R product hR hpins hpc H vkAddr cd hside g
  | pcs => exact pcs_blockSim R product hR hpins hpc H vkAddr cd g
  | finalPairing => exact fp_blockSim R product hR hpins hpc H vkAddr cd g
  | traceReturn => exact tr_blockSim R product H vkAddr g cd

/-- **THE SEVEN PROGRESS ROWS OF EVERY VALID RENDER, PROVED from the per-block rows.** The
    TraceReturn row is the tree's, with its pin read off `Valid.returnMptr`. -/
theorem prog_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) :
    R.ProgContracts product := by
  intro hR hpins hpc hcodec H vkAddr cd hacc hcomp q
  cases q with
  | vkLoading => exact vk_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | transcriptParser => exact tp_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | lagrange => exact lag_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | quotientLin => exact q_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | pcs => exact pcs_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | finalPairing => exact fp_blockProgS R product hR hpins hpc hcodec H vkAddr cd hacc hcomp
  | traceReturn => exact tr_blockProgS R product hR.returnMptr H vkAddr cd

/- NO `simPins_of_valid`. `(hR : R.Valid) : SimPins R` is REFUTED by `simPins_not_of_valid` (§2)
   whenever `Valid` is inhabited, so it is not stated, not even with a `sorry` (rule W13).
   `SimPins R` is obtained where it really comes from: the headline's codec hypothesis and one
   program fact, through `simPins_of_laws` (§2), as RECON.2 step 4 intends. -/

/-- PREMISE GAP PG-EXIT [V3: `ValidV3.exitDiscipline`, StatementsV3.lean:634; or a lemma about the
    emitters: none of them prints `return`, `stop` or `selfdestruct` outside
    `emitTraceReturnBlock`]. `SoundnessV3.lean:893` calls it "a candidate fourteenth clause". -/
theorem exitOk_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) : R.ExitOk := by
  sorry

/-- **`rows_correct`, IN THE FORM OF THE M6 EXIT GATE** (PLAN-V3 §5 M6), in the tree's present
    vocabulary. NO `SimPins R` conjunct: it is not a consequence of validity
    (`simPins_not_of_valid`). The last two conjuncts are PROVED from the per-block rows; the first
    is the premise gap above.

    `TotalV3 R product`, the gate's third conjunct, is NOT a conjunct here although `TotalV3` is
    importable: its proof (`total_correct`, §10) needs `hasMultiPointSet R = true`, which `Valid`
    does not carry (RECON.1 puts it in `programOk`, i.e. inside `ValidV3`). It is the separate
    theorem `rows_total` (§10); once `hR : R.ValidV3` supplies that fact the two join into the
    gate's statement with no new obligation. -/
theorem rows_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid) :
    R.ExitOk ∧ R.SimContracts product ∧ R.ProgContracts product :=
  ⟨exitOk_of_valid R hR, sim_rows R product, prog_rows R product⟩

/-- **THE GENERIC HEADLINE NEEDS NOTHING BEYOND THE ROWS AND ITS OWN CODEC HYPOTHESIS. PROVED**
    through `lowering_equivalence_of_stages` (SoundnessV3.lean:1226): no fixture, no further leaf.
    `SimPins R` is DERIVED (`simPins_of_laws`) from the four headline laws
    (`G1CodecHeadlineLaws`, a hypothesis of every conjunct of `LoweringEquivalenceV3`) and from
    `hasMultiPointSet R` (a `programOk` clause after RECON.1); it is neither a conjunct of `hrows`
    nor a consequence of `hR`.

    RE-POINT AT RECON.2. Step 6 of card RECON.2 DELETES `lowering_equivalence_of_stages`. This
    corollary must then be re-pointed at `lowering_equivalenceV3_of` (StatementsV3.lean:882),
    applied to `twoOutcomes_of_scans` (:581; replaces the `ExitOk` route), RECON.2's
    `rejectsV3_of_sims` (here: `rejectsV3_of_rows`), RECON.2's `completeV3_of_progs` and
    `total_correct` / `rows_total` (§10). Its conclusion becomes `LoweringEquivalenceV3 R product`,
    and `hlaws` moves inside the conclusion (it is the fourth hypothesis of that definition). -/
theorem lowering_correct_of_rows
    (hrows : ∀ (R : Render p G₁ G₂ Gₜ) (product : PairingProduct), R.Valid →
      R.ExitOk ∧ R.SimContracts product ∧ R.ProgContracts product)
    (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hlaws : Midfall.LoweringV3.G1CodecHeadlineLaws R.E.g1)
    (hmp : hasMultiPointSet R = true) :
    LoweringEquivalence R product := by
  obtain ⟨hexit, hsim, hprog⟩ := hrows R product hR
  exact lowering_equivalence_of_stages R product hR (simPins_of_laws R hlaws hmp) hexit hsim hprog

/-- The headline in the tree's present vocabulary (`Valid`, `LoweringEquivalence`), under the V3
    headline's codec laws. Without `hlaws` the statement is not provable: the frozen
    `LoweringEquivalence` carries no codec hypothesis in conjunct 1 (D-10), and
    `simPins_not_of_valid` shows validity does not supply one. -/
theorem lowering_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hlaws : Midfall.LoweringV3.G1CodecHeadlineLaws R.E.g1)
    (hmp : hasMultiPointSet R = true) :
    LoweringEquivalence R product :=
  lowering_correct_of_rows rows_correct R product hR hlaws hmp

/-- The V3 soundness obligation from the same rows, with `SimPins` taken where V3 has it (the
    headline's codec laws). PROVED: `RejectsV3` needs no row beyond `SimContracts`. -/
theorem rejectsV3_of_rows (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hmp : hasMultiPointSet R = true) : Midfall.LoweringV3.RejectsV3 R product := by
  intro W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hcodec hside hna hobs
  exact rejects_of_sims R product hR (simPins_of_laws R hcodec hmp) (sim_rows R product)
    W Lyt H vkAddr cd st₀ hdep hentry.toV2 hpc hside hna g obs hobs

/-! ## 10. Totality (TOT.1), for every render

  `TotalV3` (StatementsV3.lean:872): from every entry frame, under the honest precompiles and any
  total gas oracle, the body has a run. Decomposition:
    (1) the program executes no `gas()`: `GasFree`, then `runBody_gas_oblivious`;
    (2) per block, a run EXISTS from the boundary a run can actually be at (`LivePre`), and ends
        at the next such boundary or stops: `block_live`;
    (3) the same for the prefix: `prefix_live`;
    (4) composition: PROVED below. -/

/-- The scan that replaces TOT.1's "decidable scan of the literal program": no `gas()` anywhere,
    function bodies included. Structural in the fuel, like `Bridge.noWritersScan`. -/
def gasFreeScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc =>
    match sc with
    | .e (.lit _) => true
    | .e (.var _) => true
    | .e (.builtin op args) => !(op == EVM.Op.gas) && gasFreeScan n (.es args)
    | .e (.call _ args) => gasFreeScan n (.es args)
    | .es [] => true
    | .es (e :: rest) => gasFreeScan n (.e e) && gasFreeScan n (.es rest)
    | .s (.block body) => gasFreeScan n (.b body)
    | .s (.funDef _ _ _ body) => gasFreeScan n (.b body)
    | .s (.letDecl _ none) => true
    | .s (.letDecl _ (some e)) => gasFreeScan n (.e e)
    | .s (.assign _ e) => gasFreeScan n (.e e)
    | .s (.cond c body) => gasFreeScan n (.e c) && gasFreeScan n (.b body)
    | .s (.switch c cases dflt) =>
        gasFreeScan n (.e c) && gasFreeScan n (.cs cases) &&
          (match dflt with | none => true | some d => gasFreeScan n (.b d))
    | .s (.forLoop init c post body) =>
        gasFreeScan n (.b init) && gasFreeScan n (.e c) &&
          gasFreeScan n (.b post) && gasFreeScan n (.b body)
    | .s (.exprStmt e) => gasFreeScan n (.e e)
    | .s .break => true
    | .s .continue => true
    | .s .leave => true
    | .b [] => true
    | .b (s :: ss) => gasFreeScan n (.s s) && gasFreeScan n (.b ss)
    | .cs [] => true
    | .cs ((_, b) :: rest) => gasFreeScan n (.b b) && gasFreeScan n (.cs rest)

/-- A block executes no `gas()`. -/
def GasFree (b : Block EVM.Op) : Prop := ∃ n, gasFreeScan n (.b b) = true

/-- The scan is not vacuous. -/
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.gas []])]) = false := by decide
example : gasFreeScan 20 (.b [Stmt.exprStmt (Expr.builtin EVM.Op.pop
    [Expr.builtin EVM.Op.msize []])]) = true := by decide

/-- PREMISE GAP PG-GAS [V3: add `gasFree` to `programOk` next to `noWriters`; or a lemma about
    the emitters: none prints `Op.gas` - every gas argument is a table constant or a computed
    numeral (GenAst.lean:280, :435, :476, :513; GenAstPcs.lean:468, :493-511)]. `SupportedV2`
    excludes the three features that print `gas()` (trace, gas checkpoints, the external
    evaluator) but no clause says the program is free of it. -/
theorem gasFree_of_valid (R : Render p G₁ G₂ Gₜ) (hR : R.Valid) (vkAddr : U256) :
    GasFree (R.prog vkAddr 0) := by
  sorry

/-- A program without `gas()` has the same runs under every gas oracle. LEAF TOT.1.a: one `Step`
    induction, the shape of `Bridge.Run_worldEq_of_noWriters`; generic in the block. -/
theorem runBody_gas_oblivious (R : Render p G₁ G₂ Gₜ) (vkAddr : U256)
    (hgas : GasFree (R.prog vkAddr 0)) (c : ExternalCalls) (g g' : ExternalGas)
    (st₀ : EvmState) (obs : Obs) (h : RunBody R vkAddr 0 c g st₀ obs) :
    RunBody R vkAddr 0 c g' st₀ obs := by
  sorry

section Live

variable {D : YulSemantics.Dialect} [DecidableEq D.Value]

/-- A run that stops early is a run of any extension. PROVED. -/
theorem stmts_append_stop {funs : FunEnv D} {a b : Block D.Op} :
    ∀ {V : VEnv D} {st : D.State} {V' : VEnv D} {st' : D.State} {o : Outcome},
      ExecStmts D funs V st a V' st' o → o ≠ .normal →
        ExecStmts D funs V st (a ++ b) V' st' o := by
  induction a with
  | nil =>
      intro V st V' st' o h hne
      cases h
      exact absurd rfl hne
  | cons s rest ih =>
      intro V st V' st' o h hne
      cases h with
      | seqCons hs hrest => exact Step.seqCons hs (ih hrest hne)
      | seqStop hs hne' => exact Step.seqStop hs hne'

/-- A run exists, and it ends normally at `mid` or stops. -/
def LiveTo (funs : FunEnv D) (b : Block D.Op) (pre mid : VEnv D → D.State → Prop) : Prop :=
  StmtsContract funs b pre (fun _ _ V' st' o => (o = .normal ∧ mid V' st') ∨ o ≠ .normal)

/-- Liveness composes. PROVED. -/
theorem live_append {funs : FunEnv D} {a b : Block D.Op}
    {pre mid mid' : VEnv D → D.State → Prop}
    (ha : LiveTo funs a pre mid) (hb : LiveTo funs b mid mid') :
    LiveTo funs (a ++ b) pre mid' := by
  intro V st hpre
  obtain ⟨V₁, st₁, o₁, h₁, hpost⟩ := ha V st hpre
  rcases hpost with ⟨ho, hmid⟩ | hne
  · subst ho
    obtain ⟨V', st', o, h₂, hpost₂⟩ := hb V₁ st₁ hmid
    exact ⟨V', st', o, stmts_append_run h₁ h₂, hpost₂⟩
  · exact ⟨V₁, st₁, o₁, stmts_append_stop h₁ hne, Or.inr hne⟩

end Live

/-- The boundary a run can be at. No block before PCS exits normally with `success = 0` (the three
    of them that can lower it end with a reverting guard), so up to `.quotient` the boundary is
    clean; from `.pcs` on it may be poisoned. Liveness from a poisoned boundary is NOT asked of the
    quotient block: its interpreter loop is driven by memory a poisoned boundary says nothing
    about. -/
def LivePre (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) :
    Prop :=
  match k with
  | .pcs | .pairing => Mid R H vkAddr cd k V st
  | _ => StageInv R H vkAddr cd k V st

/-- One block is live under the honest precompiles. -/
def BlockLive (R : Render p G₁ G₂ Gₜ) (q : Partial) (H : Hash) (vkAddr : U256)
    (product : PairingProduct) (cd : Bytes) : Prop :=
  LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
    (R.scope _ _) (R.slice q)
    (fun V st => LivePre R H vkAddr cd q.pre V st)
    (fun V st => LivePre R H vkAddr cd q.pre.next V st)

/-- **PER-BLOCK EXISTENCE, FOR EVERY RENDER.** LEAVES TOT.1.b-h, one per block: the existence form
    of the loop rule (GEN.3) at each loop, the existence form of each helper summary, the honest
    relation answering at the four precompile addresses (`callsOf_graph`, P1_Exec.lean), and the
    block's all-runs row to classify the exhibited run. -/
theorem block_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hpins : SimPins R) (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (q : Partial) : BlockLive R q H vkAddr product cd := by
  sorry

/-- **PREFIX EXISTENCE.** LEAF TOT.1.i (with SIM.6: the ABI guard and the memory guard each revert
    or pass; both are runs). -/
theorem prefix_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) (R.preBlock vkAddr)
      (fun V st => V = [] ∧ st = st₀)
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st) := by
  sorry

/-- The seven slices are live. PROVED from `block_live`. -/
theorem slices_live (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (H : Hash)
    (vkAddr : U256) (cd : Bytes) (h7 : ∀ q : Partial, BlockLive R q H vkAddr product cd) :
    LiveTo (D := Bridge.Dialect (callsOf product) (ExternalGas.ofFun fun _ => 0))
      (R.scope _ _) R.slices
      (fun V st => LivePre R H vkAddr cd Checkpoint.start V st)
      (fun V st => LivePre R H vkAddr cd Checkpoint.pairing V st) :=
  live_append (live_append (live_append (live_append (live_append (live_append
    (h7 .vkLoading) (h7 .transcriptParser)) (h7 .lagrange)) (h7 .quotientLin)) (h7 .pcs))
    (h7 .finalPairing)) (h7 .traceReturn)

/-- **TOTALITY FOR EVERY RENDER, PROVED from the four named leaves** (`gasFree_of_valid`,
    `runBody_gas_oblivious`, `block_live`, `prefix_live`). `SimPins` is taken from the headline's
    codec laws, as V3 does. -/
theorem total_correct (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hmp : hasMultiPointSet R = true) : Midfall.LoweringV3.TotalV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec g _hg
  have hpins : SimPins R := simPins_of_laws R hcodec hmp
  have hlive := live_append
    (prefix_live R product hR W Lyt H vkAddr cd st₀ hdep hentry.toV2)
    (slices_live R product H vkAddr cd
      (fun q => block_live R product hR hpins hpc H vkAddr cd q))
  obtain ⟨V', st', o, hrun, _⟩ := hlive [] st₀ ⟨rfl, rfl⟩
  exact ⟨_, runBody_gas_oblivious R vkAddr (gasFree_of_valid R hR vkAddr) _ _ g st₀ _
    (run_join R vkAddr _ _ st₀ V' st' o hrun)⟩

/-- **THE TOTALITY HALF OF THE M6 EXIT GATE**, named next to `rows_correct` (which cannot carry it
    as a conjunct under `hR : R.Valid` alone: see its docstring). It IS `total_correct`. -/
theorem rows_total (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : R.Valid)
    (hmp : hasMultiPointSet R = true) : Midfall.LoweringV3.TotalV3 R product :=
  total_correct R product hR hmp

/-! ## The leaf register -/

#cone_sorries Midfall.LoweringV2.V3.Gen.rows_correct
#cone_sorries Midfall.LoweringV2.V3.Gen.rows_total
#print axioms Midfall.LoweringV2.V3.Gen.simPins_not_of_valid
#print axioms Midfall.LoweringV2.V3.Gen.simPins_of_laws
#print axioms Midfall.LoweringV2.V3.Gen.lowering_correct_of_rows
#print axioms Midfall.LoweringV2.V3.Gen.identityCorrespondence_of_bridge_fixed
#print axioms Midfall.LoweringV2.V3.Gen.pcs_slice_of_fault
#print axioms Midfall.LoweringV2.V3.Gen.live_append
#print axioms Midfall.LoweringV2.V3.Gen.lagInner_length
#print axioms Midfall.LoweringV2.V3.Gen.fail_is
#print axioms Midfall.LoweringV2.V3.Gen.batch_invert_is
#print axioms Midfall.LoweringV2.V3.Gen.helpers_are
#print axioms Midfall.LoweringV2.V3.Gen.helpers_eq
#print axioms Midfall.LoweringV2.V3.Gen.lag_sq_loop_form
#print axioms Midfall.LoweringV2.V3.Gen.breakCompressed_valid
#print axioms Midfall.LoweringV2.V3.Gen.total_correct

end Midfall.LoweringV2.V3.Gen

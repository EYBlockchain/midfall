/-
  StatementsV3 (SCRATCH - design area "statements", PLAN-V3)

  THE REPAIRED STATEMENT SURFACE, as it should read after sign-off. Typechecked against the built
  tree with `lake env lean` from formal/. Nothing here is in the repository.

  Naming: every repaired item carries a V3 suffix (or a new name) and lives in
  `Midfall.LoweringV3`, so nothing clashes with the frozen `Midfall.LoweringV2` text it replaces.
  `Render` itself is NOT changed: the eleven fields of `LoweringV2.Render` are reused as they are.

  Sections follow the brief:
    §G  codec laws                         (g)
    §A  calldataOfV3                       (a)
    §D  scopeV3, slicesV3, noShadow        (d)
    §J  the repaired WellFormed clause     (j)
    §N  programOk: the program checks      (RECON.1: the seven D-P71 clauses)
    §B  PlanMeta (circuitMeta + data)      (b)
    §C  PayloadAgrees                      (c)
    §I  ExitDiscipline, TwoOutcomes        (i)
    §V  ValidV3 - THE SINGLE TEXT, and its projections
    §E  EntryFrameV3                       (e)
    §F  GasTotal, the totality conjunct    (f)
    §K  LoweringEquivalenceV3, the four-obligation composition,
        HypothesesInhabitedV3, EndToEndV3                            (h), (k)

  DEFINITIONS are real. THEOREMS that are obligations of the plan are stated and `sorry`ed, each
  with the experiment that discharges it; the ones that are cheap are PROVED here.

  This file imports nothing from Midfall/Instances (D-P17): the deployment measurements are in
  StatementsV3Deploy.lean, the refutations of the frozen text in StatementsV3Falsifiers.lean.
-/
import Midfall.LoweringV2.Blocks
import Midfall.LoweringV2.Generated
import Midfall.LoweringV2.ProgramLemmas
set_option autoImplicit false

namespace Midfall.LoweringV3

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## §G. The codec laws (g)

  OLD: `Assumptions/Codec.lean:75-90` `G1CodecLaws` (seven fields), a hypothesis of conjunct 2 only
  (`Statements.lean:305`) and of `BlockProgress` only (`Blocks.lean:126`).

  WHY IT IS NOT ENOUGH. `verifyMsgs` (`Native.lean:269-292`) re-serialises every decoded G1 message
  with `toCompressed` and re-reads it with `ofCompressed?` (`Transcript.lean:65-69`, `:145-151`).
  `G1CodecLaws.compressedRoundtrip` is DECODER-first, so a codec whose `ofCompressed?` is the
  constant `none` satisfies all seven laws (`CurveSurface.lean:540 g1CodecZ_laws` is that proof)
  and makes `LeanAccepts` identically false. The ENCODER-first law is what forces the re-read to
  return the point that was decoded from calldata. -/

/-- THE LAWS EVERY CONJUNCT OF THE HEADLINE NEEDS (soundness included).

    * `eipRoundtrip` - `decodeCalldata` yields `Q` with `ofEip? b = some Q`; the contract absorbed
      and copied the raw bytes `b`; `Inv` compares memory with `toEip Q` (`Inv.lean:401-402`).
    * `compressedEncoderFirst` - `verifyMsgs` reads back `ofCompressed? (toCompressed Q)`; without
      this law it reads `none` (Lean rejects everything) or another point (finding A-4).
    * `compressedWidth` - the transcript cursor advances by `g1CompressedWidth` per G1 read
      (`Transcript.read`), so a wrong width misaligns every later read.
    * `toEip_one` - the committed-instance commitment is absorbed by the contract as 128 zero
      bytes (`TranscriptProofParser.yul:36-46`) and by Lean as `toEip 1`; the `g1_identity`
      window of `Inv` is the same pin. -/
structure G1CodecHeadlineLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth
  toEip_one : c.toEip 1 = natToBytesBE 0 128

/-- THE FULL BUNDLE `EndToEndV3` NEEDS: the seven frozen laws plus the encoder-first one. The four
    extra laws over `G1CodecHeadlineLaws` are consumed by the calldata round trip only:
    `compressedRoundtrip` by `verifyNative_iff_msgs_codec` (`Obligations.lean:832`) and
    `repack_spec_of_decodeRust` (`Calldata.lean:1276`); `ofEip_toEip`, `eipShape`, `eipWidth` by
    `calldata_roundtrip` (`Calldata.lean:731`). -/
structure G1CodecLawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop
    extends G1CodecLaws c where
  compressedEncoderFirst : ∀ Q : G₁, c.ofCompressed? (c.toCompressed Q) = some Q

/-- The full bundle gives the headline bundle. PROVED. -/
theorem G1CodecLawsV3.headline {G₁ : Type} [Group G₁] {c : G1Codec G₁} (h : G1CodecLawsV3 c) :
    G1CodecHeadlineLaws c :=
  ⟨h.eipRoundtrip, h.compressedEncoderFirst, h.compressedWidth, h.toEip_one⟩

/-- A codec whose compressed half is `comp`, with the decoder chosen classically. This is the
    shape `g1zOfEip?` already has for the EIP half (`G1Agreement.lean:1996`). -/
noncomputable def withCompressed {G₁ : Type} (c : G1Codec G₁) (comp : G₁ → Bytes) : G1Codec G₁ :=
  { c with
    toCompressed := comp
    ofCompressed? := fun b =>
      open Classical in if h : ∃ Q, comp Q = b then some (Classical.choose h) else none }

/-- WITNESS (joint satisfiability, generic). Any codec satisfying the seven frozen laws becomes a
    codec satisfying all eight once its compressed half is replaced by an INJECTIVE map of the
    right width. PROVED: so the V3 law set is satisfiable wherever the frozen one is and an
    injection `G₁ → 48 bytes` exists. `StatementsV3Deploy.lean` instantiates it at `G₁z`. -/
theorem withCompressed_lawsV3 {G₁ : Type} [Group G₁] (c : G1Codec G₁) (hc : G1CodecLaws c)
    (comp : G₁ → Bytes) (hinj : Function.Injective comp)
    (hw : ∀ Q, (comp Q).size = g1CompressedWidth) : G1CodecLawsV3 (withCompressed c comp) where
  eipRoundtrip := hc.eipRoundtrip
  compressedRoundtrip := by
    intro b Q h
    simp only [withCompressed] at h
    by_cases hex : ∃ Q, comp Q = b
    · simp only [hex, ↓reduceDIte] at h
      have hQ : Classical.choose hex = Q := Option.some.inj h
      rw [← hQ]
      exact Classical.choose_spec hex
    · simp only [hex, ↓reduceDIte] at h
      cases h
  ofEip_toEip := hc.ofEip_toEip
  eipShape := hc.eipShape
  toEip_one := hc.toEip_one
  compressedWidth := hw
  eipWidth := hc.eipWidth
  compressedEncoderFirst := by
    intro Q
    have hex : ∃ Q', comp Q' = comp Q := ⟨Q, rfl⟩
    simp only [withCompressed, hex, ↓reduceDIte]
    exact congrArg some (hinj (Classical.choose_spec hex))

/-! ## §A. calldataOfV3 (a)

  OLD (`Statements.lean:335-340`):
      (repackProof plan R.E.g1 π).mapError fromRepackError >>= fun π' =>
        encodeCalldata R.cfg.numInstances plan R.E.g1 π' inst
  `Lowering.encodeCalldata` (`Calldata.lean:241-250`) repacks its proof argument AGAIN, so the
  second repack sees `repackedLen` bytes where it demands `compressedLen` and throws
  `lengthMismatch`. The frozen term never returns `.ok`.

  NEW: the tree's own intended composition, `Lowering.repackThenEncode` (`Calldata.lean:257`). -/

/-- The calldata the ported repacker and encoder produce for a compressed proof. -/
def calldataOfV3 (R : Render p G₁ G₂ Gₜ) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  Midfall.Lowering.repackThenEncode (p := p) R.cfg.numInstances
    (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π inst

/-- The FROZEN composition, as a function of exactly the three things it reads off the render, so
    that it can be EVALUATED on the in-tree toy data (a `Render` needs a prime-order group and
    a pairing; `CdKats.ToyG` is a two-point type). PINNED VERBATIM AS OF ST.4 (the D-P27 pattern:
    an amended frozen statement keeps its old text as a named definition next to the exhibit that
    shows why it was wrong): until ST.4 the live `LoweringV2.calldataOf` WAS this term, by `rfl`,
    and the bridge lemma said so. From ST.4 on the live def is `repackThenEncode`, the bridge is
    false and is gone, and this core is what the falsifier `frozenCalldata_isOk` evaluates. -/
def frozenCalldataCore {G : Type} (numInstances : Nat) (plan : RepackedProofLayoutPlan)
    (c : G1Codec G) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  (Midfall.Lowering.repackProof (p := p) plan c π).mapError
      Midfall.Generator.GeneratorError.fromRepackError >>= fun π' =>
    Midfall.Lowering.encodeCalldata (p := p) numInstances plan c π' inst


section CalldataWitness
open Midfall.Lowering.CdKats
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- WITNESS for (a): on the toy data the repaired composition returns `.ok`, the result is the
    tree's canonical `Lowering.calldataOf` of the toy messages, and `decodeCalldata` reads it
    back. `katLayout`'s plan is `katPlan` (the last conjunct), so this is the composition
    `calldataOfV3` performs. -/
def calldataOfV3_witness_ok : Bool :=
  (match Midfall.Lowering.repackThenEncode (p := 17) 1 katPlan toyCodec katCompressed #[5] with
   | .ok cd =>
       cd == Midfall.Lowering.calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 5] &&
       (match Midfall.Lowering.decodeCalldata (p := 17) katLayout 1 toyCodec cd with
        | some (ms, inst) => ms.map msgCode == katMsgs.map msgCode && inst.toList.map BitVec.toNat == [5]
        | none => false)
   | .error _ => false) &&
  (RepackedProofLayoutPlan.fromProofLayout katLayout).slots == katPlan.slots

#eval calldataOfV3_witness_ok   -- expect true

/-- FALSIFIER for the frozen text, at the same data: `.ok` never comes back. -/
def frozenCalldata_isOk : Bool :=
  match frozenCalldataCore (p := 17) 1 katPlan toyCodec katCompressed #[5] with
  | .ok _ => true
  | .error _ => false

#eval frozenCalldata_isOk   -- expect false

end CalldataWitness

/-! ## §D. The block scope and the slice decomposition (d)

  OLD (`Statements.lean:107-110`): `Render.scope c g := [hoist D R.helpers]`, with the docstring
  "the only funDefs of the program". FALSE for the generator's text: `q_program_fail` and `q_pow5`
  are defined inside the quotient region (token indices 3814 and 3837 of
  `mainAssemblyTokens poseidonM`), so once WP-G1 emits them `lookupFun (R.scope c g) "q_pow5"` is
  `none` and no slice run through that call exists.

  TWO CANDIDATES were measured (`ProbeScope.lean`):
    A. `[hoist D (R.prog 0 0)]`                       - `fail_lookup ... := rfl` FAILS for generic R
    B. `[hoist D R.helpers ++ hoist D R.slices]`      - `fail_lookup ... := rfl` still holds
  `Blocks/TraceReturn.lean:405 fail_lookup` is the one place the tree unfolds the scope, and it
  does so by `rfl`; under A the reduction is stuck on `wrapperLocals`' `if m.embeddedVk.isNone`.
  B is A up to the structural lemma `hoist_prog_eq_scopeV3` below, is address-independent by
  construction (no `hoist_prog_addr_indep` needed to state it), and keeps every existing lookup.
  V3 takes B. -/

/-- The seven slices in include order. Moved from `Blocks.lean:202` (refinable) into the statement
    surface, because the scope is now defined through it. Same text. -/
def slicesV3 (R : Render p G₁ G₂ Gₜ) : YulBlock :=
  R.slice .vkLoading ++ R.slice .transcriptParser ++ R.slice .lagrange ++
    R.slice .quotientLin ++ R.slice .pcs ++ R.slice .finalPairing ++ R.slice .traceReturn

/-- It is the definition `Blocks.lean` already uses. -/
theorem slicesV3_eq (R : Render p G₁ G₂ Gₜ) : slicesV3 R = R.slices := rfl

/-- THE FUNCTION SCOPE EVERY BLOCK RUNS IN: every function the closed program defines at its top
    level - the inlined helpers, then whatever the slices define (the quotient region's
    `q_program_fail`, `q_pow5`, `q_limb7*`). -/
def scopeV3 (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) :
    FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) R.helpers ++ hoist (Bridge.Dialect c g) (slicesV3 R)]

/-- NO SHADOWING, decidably: no top-level binder of the un-inlined program is a constant name.
    This is the side condition of `inline_append` (`ProgramLemmas.lean:27`), without which
    `prog_slices_decomp` is false (findings B-5, D-13: a model constant named `r` is substituted in
    the standalone slices and not in the program). solc rejects such shadowing, so the clause also
    aligns the model with Solidity. -/
def noShadowCore (pv : PlanView) (m : Model) : Bool :=
  (topBinders (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv m)).all
    fun x => !((constTableOf m).map Prod.fst).contains x

/-- The render-level face of `noShadowCore`. -/
def noShadowB (R : Render p G₁ G₂ Gₜ) : Bool := noShadowCore R.pv R.model

/-- **THE STRUCTURAL DECOMPOSITION, RESTATED** (replaces `Blocks.lean:220 prog_slices_decomp`).
    Conjunct 1 is unchanged but now carries the no-shadow hypothesis it needs. Conjunct 2 was
    `hoist prog = hoist helpers` (false once the quotient functions are emitted) and is now "the
    hoisted program scope is the block scope".

    OBLIGATION (WP-A2). Experiment that discharges it: `inline_append` five times against
    `noShadowB`, `List.filterMap_append` for `hoist`, and `hoist (preSlice) = []`,
    `hoist (mainLocalsInlined) = []` (inlining maps `cond`/`letDecl` to `cond`/`letDecl`). -/
theorem prog_slices_decompV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (vkAddr qAddr : U256) (c : ExternalCalls) (g : ExternalGas) :
    R.prog vkAddr qAddr =
        R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ slicesV3 R ∧
      [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = scopeV3 R c g := by
  sorry

/-- CONSEQUENCE, PROVED from the obligation above: the frozen `hoist_prog_addr_indep`
    (`Blocks.lean:145`, sorried) is no longer a separate hole. -/
theorem hoist_prog_addr_indepV3 (R : Render p G₁ G₂ Gₜ) (hns : noShadowB R = true)
    (c : ExternalCalls) (g : ExternalGas) (a b a' b' : U256) :
    hoist (Bridge.Dialect c g) (R.prog a b) = hoist (Bridge.Dialect c g) (R.prog a' b') := by
  have h1 := (prog_slices_decompV3 R hns a b c g).2
  have h2 := (prog_slices_decompV3 R hns a' b' c g).2
  exact List.head_eq_of_cons_eq (h1.trans h2.symm)

/-- A helper is still found where it was: the V3 scope starts with the hoisted helpers, and
    `lookupFun` short-circuits. PROVED, by the same `rfl` as `Blocks/TraceReturn.lean:405`. -/
theorem fail_lookupV3 (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} :
    lookupFun (scopeV3 R c g) "fail" =
      some ({ params := ["sel"], rets := [],
              body := [Stmt.exprStmt (Expr.builtin Op.mstore
                  [Expr.lit (.number 0),
                   Expr.builtin Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
                Stmt.exprStmt (Expr.builtin Op.revert
                  [Expr.lit (.number 0), Expr.lit (.number 4)])] },
            scopeV3 R c g) := rfl

/-! ## §J. VerifyingKey.WellFormed (j)

  OLD (`Halo2/Exec/VerifyingKey.lean:99-102`):
      permutationCommitmentsMatch :
        vk.permutation.commitments.size = divCeil vk.cs.permutation.columns.size (vk.csDegree - 2)
  That is the number of permutation PRODUCT commitments the PROOF carries (one per chunk,
  `permutation/verifier.rs:41-46`). The VK holds one sigma commitment per permutation COLUMN:
  `permutation/keygen.rs:244-250` (`Vec::with_capacity(p.columns.len())`, one push per column)
  and `permutation.rs:123` (`(0..argument.columns.len())`). The Lean port itself reads
  `vk.commitments.size` evaluations (`Permutation.lean:209`). 8 against 3 at the deployment. -/

/- **`WellFormedV3` IS DELETED (RECON.1 step 4).** Its one corrected clause - one sigma commitment per
    permutation COLUMN, not `divCeil columns (csDegree - 2)` - is kept as the computation
    `permCommMatchRepaired` (§N), a conjunct of `programOkB`, because `supported` is the frozen
    `SupportedV2` and cannot gain a field. The other six clauses were verbatim
    `VerifyingKey.WellFormed` fields and are carried by `SupportedV2.wf`. At the deployment the frozen
    clause is FALSE (8 against 3, `Deploy.wellFormedPermCounts_ok`) and the repaired one is TRUE (8
    against 8): R.7 repairs the frozen predicate, at which point `permCommMatchRepaired` is
    `supported.wf.permutationCommitmentsMatch` and leaves this file. -/
/-! ## §B. The plan's circuit meta and data (b)

  OLD (`Statements.lean:186-190`):
      circuitMeta : ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances
                      = .ok R.plan.meta_
      layout      : ProofCalldataLayout.fromProtocol R.plan.meta_.protocol abiVerifyProofProofCptr
                      R.plan.meta_.numEvals R.plan.meta_.numPointSets = .ok R.plan.proofLayout
  `ConstraintSystemMeta.new` returns `numPointSets := 0` (`Encoding.lean:473`). Rust's plan meta is
  that value AFTER `meta_data_for_vk` (`vk.rs:504-519`: `set_num_dummy_evals`, then
  `set_num_point_sets(kzg::num_point_sets(&meta, &data))`), and `plan.rs:238-244` builds the proof
  layout from the post-processed count. So the frozen pair forces a layout with zero `q_eval`
  words; no faithful plan satisfies both clauses.

  NEW: clause 1 states the post-processing. Clause 2 (`layout`) keeps its text. -/

/-- `vk.rs:504-519` at `Features.solidity` (`outer-fewer-point-sets` off, so `n_dummy = 0`): the
    meta the plan carries is the raw meta with the dummy count set to 0 and the point-set count
    set to `kzg::num_point_sets` of the data built from it; and the data is `Data::new` of that
    same pre-point-set meta. `m0` is the raw meta, `n` the point-set count.

    `Data.new` is given `R.plan.memory`. Rust gives it the intermediate default-config layout
    (`vk.rs:512-514`); `Data.new` reads ten base pointers of the layout (`Encoding.lean:626-639`)
    and at the deployment the two layouts agree on all ten (measured, `ProbeStable.lean`). That
    this holds for every render is NOT settled here; WP-G4's port of `LoweringPlan::new` replaces
    this clause by an equation with the ported constructor. -/
def PlanMeta (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ (m0 : ConstraintSystemMeta) (n : Nat),
    ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok m0 ∧
    Data.new (m0.setNumDummyEvals 0) R.plan.vk R.plan.memory = .ok R.plan.data ∧
    numPointSets (m0.setNumDummyEvals 0) R.plan.data = .ok n ∧
    R.plan.meta_ = (m0.setNumDummyEvals 0).setNumPointSets n

/-- The decidable face of the two clauses that do not mention `Data` equality (`Data` derives no
    `BEq`): what `StatementsV3Deploy.lean` evaluates. `cs` and `nci` are `R.vk.cs` and
    `R.cfg.numCommittedInstances`. -/
def planMetaB {F : Type} (cs : ConstraintSystem F) (nci : Nat) (plan : LoweringPlan Unit Unit) :
    Bool :=
  match ConstraintSystemMeta.new Features.solidity cs nci with
  | .error _ => false
  | .ok m0 =>
    match numPointSets (m0.setNumDummyEvals 0) plan.data with
    | .error _ => false
    | .ok n => plan.meta_ == (m0.setNumDummyEvals 0).setNumPointSets n

/-- The decidable face of the (unchanged) `layout` clause. -/
def planLayoutB (plan : LoweringPlan Unit Unit) : Bool :=
  match ProofCalldataLayout.fromProtocol plan.meta_.protocol abiVerifyProofProofCptr
      plan.meta_.numEvals plan.meta_.numPointSets with
  | .ok l => l == plan.proofLayout
  | .error _ => false

/-- The decidable face of the FROZEN clause 1, for the comparison table. -/
def frozenCircuitMetaB {F : Type} (cs : ConstraintSystem F) (nci : Nat)
    (plan : LoweringPlan Unit Unit) : Bool :=
  match ConstraintSystemMeta.new Features.solidity cs nci with
  | .ok m => m == plan.meta_
  | .error _ => false

/-! ## §C. The payload-content pins (c)

  OLD: `Valid.slots : EnvAgrees ...` (`Statements.lean:205`, `Inv.lean:533-579`) ties the payload
  `R.pv.vk` to the Lean key through ONE word, `vkDigestWord`. v1 had `VkSlotsAgree`
  (`Inv.lean:608-634`) for the three base slots; V2 dropped it. Nothing pins the commitment words,
  the domain words, or `E.delta`. -/

/-- Header word `i` of the payload image. `getD` past the end is the zero word, so a pin about a
    slot the payload does not have is false for every non-zero expected value. -/
def payloadWord (PV : PlanView) (i : Nat) : Word256 := (PV.vk.constants.getD i ("", 0)).2

/-- The 128-byte EIP-2537 image of one payload commitment: `x_hi ‖ x_lo ‖ y_hi ‖ y_lo`, the order
    `Halo2VerifyingKey.bytes` writes (`Models.lean:475-481`). -/
def g1WordsBytes (w : G1Words) : Bytes :=
  wordToBytesBE w.xHi ++ wordToBytesBE w.xLo ++ wordToBytesBE w.yHi ++ wordToBytesBE w.yLo

/-- **THE PAYLOAD AGREES WITH THE LEAN KEY.** One structure for every payload word the contract
    reads and every environment constant the generator emits as a literal. Slot numbers are
    `vkHeaderTemplateSlotsDefault`'s (`Models.lean:734`), never literals. `vkDigest` (slot 0) is
    NOT repeated here: it stays `EnvAgrees.vkDigestWord`. -/
structure PayloadAgrees (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- The object text's first field (card step 3): header word 0 is the Lean key's transcript
      representation. THE OVERLAP IS KEPT BECAUSE THE CARD NAMES THE FIELD: `EnvAgrees.vkDigestWord`
      (`Inv.lean:579`) states the same equation, and the 18-clause text omitted it here for that
      reason. It is redundant with `env`, not with `generated`. -/
  digest : payloadWord R.pv vkHeaderTemplateSlotsDefault.vkDigest =
    frWord R.vk.transcriptRepr
  /-- Justifies `eq(mload(NUM_INSTANCES_MPTR), <num_instances>)` in VkLoading (progress: the
      guard passes) - slot 1. -/
  numInstances : payloadWord R.pv vkHeaderTemplateSlotsDefault.numInstances =
    BitVec.ofNat 256 R.cfg.numInstances
  /-- Justifies `eq(mload(K_MPTR), <k>)` in VkLoading - slot 2. -/
  k : payloadWord R.pv vkHeaderTemplateSlotsDefault.k = BitVec.ofNat 256 R.vk.domain.k
  /-- Justifies `mload(N_INV_MPTR)` in Lagrange (`l_i_common := mulmod(x_n_minus_1, N_INV, r)`);
      Lean uses `barycentricWeight`, tied to this value by `EnvAgrees.baryWeight` - slot 3. -/
  nInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.nInv =
    frWord ((((2 ^ R.vk.domain.k : ℕ) : Fr p))⁻¹)
  /-- Justifies `mload(OMEGA_MPTR)` in Lagrange (the `x - omega^i` walk) and in the PCS rotation
      points; Lean rotates by `vk.domain.omega` - slot 4. -/
  omega : payloadWord R.pv vkHeaderTemplateSlotsDefault.omega = frWord R.vk.domain.omega
  /-- Justifies `mload(OMEGA_INV_MPTR)` in the PCS rotation points (negative rotations) -
      slot 5. -/
  omegaInv : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInv =
    frWord R.vk.domain.omegaInv
  /-- Justifies `mload(OMEGA_INV_TO_L_MPTR)`, the start of both Lagrange loops:
      `omega_inv ^ |rotation_last|` (`Vk.lean:724-726`, VK:115-118) - slot 6. -/
  omegaInvToL : payloadWord R.pv vkHeaderTemplateSlotsDefault.omegaInvToL =
    frWord (R.vk.domain.omegaInv ^ R.plan.meta_.rotationLast.natAbs)
  /-- Justifies the four `eq(mload(*ACC*_MPTR), <literal>)` guards in VkLoading: the header's
      accumulator quadruple is the configuration's (`accWordsOfEncoding`, `Inv.lean:259`) -
      slots 7-10. -/
  accWords :
    ((payloadWord R.pv vkHeaderTemplateSlotsDefault.hasAccumulator).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.accOffset).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbs).toNat,
      (payloadWord R.pv vkHeaderTemplateSlotsDefault.numAccLimbBits).toNat) =
    accWordsOfEncoding R.cfg.accumulator
  /-- Justifies `mcopy(_, G1_BASE_MPTR, 0x80)` in the PCS final MSM (the `-v * G` term): the slot
      holds the encoding of the generator Lean's `DualMSM` uses (`P.g₁`). v1
      `VkSlotsAgree.g1BaseWords` - slot 11. -/
  g1Base : vkG1Words R.pv vkG1BaseSlot = R.E.g1.toEip P.g₁
  /-- Justifies `mcopy(add(scratch, 0x80), G2_BASE_MPTR, 0x100)` in `ec_pairing`. v1
      `VkSlotsAgree.g2BaseWords` - slot 15. -/
  g2Base : vkG2Words R.pv vkG2BaseSlot = R.encG2 P.g₂
  /-- Justifies `mcopy(add(scratch, 0x200), NEG_S_G2_BASE_MPTR, 0x100)` in `ec_pairing`. v1
      `VkSlotsAgree.negSG2Words` - slot 23. -/
  negSG2 : vkG2Words R.pv vkNegSG2BaseSlot = R.encG2 R.sG2gen⁻¹
  /-- Justifies every read of a fixed-commitment EcPoint in the PCS MSMs (the payload section
      after the header constants): the words are the EIP encoding of the Lean key's own
      commitments, in order. -/
  fixedComms : R.pv.vk.fixedComms.map g1WordsBytes =
    R.vk.fixedCommitments.toList.map R.E.g1.toEip
  /-- Same for the permutation (sigma) commitments, the last payload section. -/
  permutationComms : R.pv.vk.permutationComms.map g1WordsBytes =
    R.vk.permutation.commitments.toList.map R.E.g1.toEip
  /- **`delta` IS DROPPED (card step 3).** The 18-clause text pinned the emitted `frDelta` literal
      against `R.E.delta`; the single text does not, because `generated` already pins `R.E.delta`
      against the program: OBJ.7's gate 9 (`GeneratedKats.generateAll_falsifierDeltaAndOmega_ok`)
      measures that `delta := 2` changes the generated text AND the quotient blocks, so DELTA reaches
      the text through the generator and not through a payload equation - and `inputs.frDelta` alone is
      INERT at the deployment (`Artifacts.lean:129-135`: the one template site that interpolates it is
      inside the `when None` arm P-13c never renders; `Deploy.frDeltaIsGeneratorPow_ok` measures the literal's own value
      halves). The card's acceptance line - "`delta := 2` falsifies `generated` (not `payload`)" - is
      gate 9, and `Deploy.recon1_programOkB_ok` measures the bundle that reads the table. -/

/-- The decidable face of the seven fields that mention no codec and no group element: the header
    scalars (`digest` included) and the accumulator quadruple. `StatementsV3Deploy.lean` evaluates it. The
    five remaining fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`, `permutationComms`) compare
    payload bytes with `toEip` of group elements: each needs a codec fact (`toEip` is
    noncomputable at `g1CodecZ`) and, for the three base slots, a pairing whose generators are
    pinned (finding H-2). -/
def payloadScalarsB (PV : PlanView) (numInstances k : Nat) (omega omegaInv : Fr p)
    (rotationLast : Int) (acc : Option Midfall.Generator.AccumulatorEncoding) : List Bool :=
  let s := vkHeaderTemplateSlotsDefault
  [ payloadWord PV s.numInstances == BitVec.ofNat 256 numInstances,
    payloadWord PV s.k == BitVec.ofNat 256 k,
    payloadWord PV s.nInv == frWord ((((2 ^ k : ℕ) : Fr p))⁻¹),
    payloadWord PV s.omega == frWord omega,
    payloadWord PV s.omegaInv == frWord omegaInv,
    payloadWord PV s.omegaInvToL == frWord (omegaInv ^ rotationLast.natAbs),
    ((payloadWord PV s.hasAccumulator).toNat, (payloadWord PV s.accOffset).toNat,
      (payloadWord PV s.numAccLimbs).toNat, (payloadWord PV s.numAccLimbBits).toNat) ==
        accWordsOfEncoding acc ]

/-! ## §I. The exit discipline and TwoOutcomes (i)

  OLD (`Blocks.lean:356-363`): `rejects_of_not_accepts`, a sorried lemma with neither `SoundSide`
  nor `R.Valid`, concluding `obs.isRevertOrHalt` from `¬ LeanAccepts`. FALSE on the logup-panic
  set (the contract accepts there, `Inv.lean:698-706`) and false for every render whose
  `cfg.numInstances` is perturbed (finding A+1).

  NEW: conjunct 3 does not need any rejection lemma. Every run of the program either returns ABI
  `true` or is a non-committing halt, with the world unchanged, WHATEVER the Lean verifier says,
  for every call relation, every gas oracle and every start state. Three syntactic facts give it:
    1. `NoWriters` (already `Valid.noWriters`) - the world is unchanged;
    2. no `stop`, `selfdestruct` or `return` builtin occurs outside the designated tail, so the
       only halts the body can produce are `revert`, `invalid`, `invalidMemoryAccess`,
       `staticViolation` - all non-committing (`HaltKind.commits`);
    3. the program ends with `mstore(p, 1)  return(p, 0x20)` and has no `leave` outside a
       function nor `break`/`continue` outside a loop, so a run that does not halt earlier
       reaches that tail and returns `abiTrue`. -/

/-- The builtins that end the frame with a COMMITTING halt. -/
def isCommittingExit : EVM.Op → Bool
  | .stop | .ret | .selfdestruct => true
  | _ => false

/-- One layer of the exit scan, in the shape of `Bridge.noWritersStep` (`Bridge.lean:1069`), with
    two context bits: inside a function body (where `leave` is legal) and inside a loop body
    (where `break` / `continue` are). -/
def exitStep (inFun inLoop : Bool) : Scan → (Bool → Bool → Scan → Bool) → Bool
  | .e (.lit _), _ => true
  | .e (.var _), _ => true
  | .e (.builtin op args), rec => !isCommittingExit op && rec inFun inLoop (.es args)
  | .e (.call _ args), rec => rec inFun inLoop (.es args)
  | .es [], _ => true
  | .es (e :: rest), rec => rec inFun inLoop (.e e) && rec inFun inLoop (.es rest)
  | .s (.block body), rec => rec inFun inLoop (.b body)
  | .s (.funDef _ _ _ body), rec => rec true false (.b body)
  | .s (.letDecl _ none), _ => true
  | .s (.letDecl _ (some e)), rec => rec inFun inLoop (.e e)
  | .s (.assign _ e), rec => rec inFun inLoop (.e e)
  | .s (.cond c body), rec => rec inFun inLoop (.e c) && rec inFun inLoop (.b body)
  | .s (.switch c cases dflt), rec =>
      rec inFun inLoop (.e c) && rec inFun inLoop (.cs cases) &&
        (match dflt with | none => true | some d => rec inFun inLoop (.b d))
  | .s (.forLoop init c post body), rec =>
      rec inFun false (.b init) && rec inFun false (.e c) && rec inFun false (.b post) &&
        rec inFun true (.b body)
  | .s (.exprStmt e), rec => rec inFun inLoop (.e e)
  | .s .break, _ => inLoop
  | .s .continue, _ => inLoop
  | .s .leave, _ => inFun
  | .b [], _ => true
  | .b (s :: ss), rec => rec inFun inLoop (.s s) && rec inFun inLoop (.b ss)
  | .cs [], _ => true
  | .cs ((_, b) :: rest), rec => rec inFun inLoop (.b b) && rec inFun inLoop (.cs rest)

/-- Fuel-bounded scan; exhaustion answers `false` (R-37), as in `noWritersScan`. -/
def exitScan : Nat → Bool → Bool → Scan → Bool
  | 0, _, _, _ => false
  | n + 1, f, l, sc => exitStep f l sc (exitScan n)

/-- The program minus its designated tail `mstore(p, 1)  return(p, 0x20)`, when it has one. -/
def returnTail? (b : Block EVM.Op) : Option (Block EVM.Op) :=
  match b.reverse with
  | Stmt.exprStmt (Expr.builtin EVM.Op.ret
        [Expr.lit (Literal.number p₁), Expr.lit (Literal.number n)]) ::
      Stmt.exprStmt (Expr.builtin EVM.Op.mstore
        [Expr.lit (Literal.number p₂), Expr.lit (Literal.number v)]) :: initRev =>
      if p₁ = p₂ ∧ n = 32 ∧ v = 1 then some initRev.reverse else none
  | _ => none

/-- The whole check: the tail is there and nothing before it can commit or escape. -/
def exitDisciplineFuel (n : Nat) (b : Block EVM.Op) : Bool :=
  match returnTail? b with
  | some init => exitScan n false false (.b init)
  | none => false

/-- The only committing exit of the block is its final `return` of the word 1. -/
def ExitDiscipline (b : Block EVM.Op) : Prop := ∃ n, exitDisciplineFuel n b = true

/-- WITNESS: the shape `traceReturn` ends the program with passes. PROVED by `decide`. -/
theorem exitDiscipline_witness :
    ExitDiscipline (yul% {
      if iszero(calldataload(0)) { mstore(0, 7) revert(0, 4) }
      mstore(4096, 1)
      return(4096, 32) }) :=
  ⟨16, by decide⟩

/-- FALSIFIERS: an early `return`, a `stop`, a missing tail and a top-level `leave` are each
    refused at the fuel that accepts the witness. PROVED by `decide`. -/
theorem exitDiscipline_refuses :
    exitDisciplineFuel 16 (yul% { return(0, 32) mstore(4096, 1) return(4096, 32) }) = false ∧
    exitDisciplineFuel 16 (yul% { if calldataload(0) { stop() } mstore(4096, 1) return(4096, 32) })
      = false ∧
    exitDisciplineFuel 16 (yul% { mstore(4096, 1) }) = false ∧
    exitDisciplineFuel 16 (yul% { mstore(4096, 2) return(4096, 32) }) = false ∧
    exitDisciplineFuel 16 (yul% { leave mstore(4096, 1) return(4096, 32) }) = false := by
  decide

/-- **TWO OUTCOMES.** Every run of the body, under ANY call relation and ANY gas oracle, from ANY
    state, returns ABI `true` with the world unchanged or is a non-committing halt with the world
    unchanged. No `LeanAccepts`, no `SoundSide`, no snapshot, no `EntryFrame`, no `Eip2537.Holds`. -/
def TwoOutcomes (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∀ (vkAddr : U256) (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (obs : Obs),
    RunBody R vkAddr 0 c g st₀ obs →
    obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)

/-- **THE OBLIGATION THAT REPLACES `rejects_of_not_accepts`** (WP-M5c). Generic in the block: no
    render, no plan, no key.

    Experiment that discharges it: one induction on `Step` (the shape of
    `Bridge.Run_worldEq_of_noWriters`, `Bridge.lean:1221`) proving, for a block passing
    `exitScan`, that every derivation ends with `halted` unchanged or set by a non-committing
    builtin and with an outcome that is `.normal`/`.halt` at top level; then
    `Step.stmts_append_inv` (`Contracts.lean:115`) at the tail and the two builtin steps
    `mstore`/`ret` by `simp [stepOp]`. `NoWriters` gives `WorldEq` (the registered
    `Run_worldEq_of_noWriters`). -/
theorem twoOutcomes_of_exitDiscipline (b : Block EVM.Op) (hw : NoWriters b) (hx : ExitDiscipline b)
    (c : ExternalCalls) (g : ExternalGas) (st₀ : EvmState) (V' : VEnv (Bridge.Dialect c g))
    (stObs : EvmState) (o : Outcome) (hrun : Bridge.RunCommitted c g b st₀ V' stObs o) :
    (⟨stObs, o⟩ : Obs).view = returnView st₀ ∨
      ((⟨stObs, o⟩ : Obs).isRevertOrHalt ∧ (⟨stObs, o⟩ : Obs).worldUnchanged st₀) := by
  sorry

/-- The two scans are insensitive to the two addresses the wrapper binds (they occur only as
    `let` literals). OBLIGATION, same cost class as `noWriters_prog` (`Blocks.lean:340`), which it
    subsumes. -/
theorem scans_prog_addr_indep (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256)
    (hw : NoWriters (R.prog 0 0)) (hx : ExitDiscipline (R.prog 0 0)) :
    NoWriters (R.prog vkAddr qAddr) ∧ ExitDiscipline (R.prog vkAddr qAddr) := by
  sorry

/-- `TwoOutcomes` from the two decidable render facts. PROVED from the two obligations above. -/
theorem twoOutcomes_of_scans (R : Render p G₁ G₂ Gₜ)
    (hw : NoWriters (R.prog 0 0)) (hx : ExitDiscipline (R.prog 0 0)) : TwoOutcomes R := by
  intro vkAddr c g st₀ obs hobs
  obtain ⟨V', hrun⟩ := hobs
  obtain ⟨hw', hx'⟩ := scans_prog_addr_indep R vkAddr 0 hw hx
  exact twoOutcomes_of_exitDiscipline (R.prog vkAddr 0) hw' hx' c g st₀ V' obs.state obs.outcome hrun

/-! ## §N. THE PROGRAM CHECKS: one decidable bundle with the seven D-P71 clauses folded in (RECON.1)

  THE BASE IS THE OBJECT TEXT (`ObjectV3Full.lean:747-755`, `programOkWith`): `codegenStruct`,
  `constsCoherent`, `callsResolved`, `noShadow`, `mainClosed`, `0x80 ≤ transcriptMptr`. RECON.1 step 2
  adds the frozen token clause (`codegenAgrees`), ONE exit scan, `cdBound` and `hasMultiPointSet`; the
  D-P71 blockquote adds `gasScan`, the transcript region (PG-TPBUF), `0x80 ≤ g1IdentityMptr`
  (PG-G1ID), `2 ≤ numNegLagranges` (PG-NEGLAG) and the repaired permutation clause that step 4 deletes
  with `WellFormedV3`. `FR_MODULUS = p` and `returnMptr` are NOT conjuncts: they are THEOREMS of
  `constsCoherent` (additions 6 and 7), proved below.

  WHY `programOk` IS A `Prop` AND NOT THE OBJECT TEXT'S `Bool`: two conjuncts - the exit scan and the
  gas scan - are fuel-bounded scans stated as `∃ n, scan n = true`, exactly as `NoWriters` is
  (`Bridge.lean:1108`). Folding them into one `Bool` would pin a fuel in the statement and make the
  class depend on the witness: a render whose program needs one more unit of fuel than the pin would
  be excluded by a number that means nothing. So `programOkB` is the decidable bundle the clause table
  evaluates and `programOk` is `programOkB = true` conjoined with the two scans. Nothing is weakened
  and nothing is invented.

  `constsCoherent`, `expectedConsts`, `callsResolved` and `noShadowProg` are the object text's, ported
  verbatim except where the tree's own names differ (`mainAsmRaw` takes the model since WP-G1;
  `FR_MODULUS` is the tree's `frModulusConstant` and not a second copy of the literal). -/

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
  , ("FR_MODULUS", frModulusConstant)
  , ("BLS_P_HI", 0x1a0111ea397fe69a4b1ba7b6434bacd7)
  , ("BLS_P_MINUS_ONE_LO", 0x64774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_0_WITH_ID_FLAG", 0xf38512bf6730d2a0f6b0f6241eabfffeb153ffffbafeffffffffaaaa)
  , ("BLS_P_MINUS_ONE_PACKED_1", 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84) ]

/-- The names the un-inlined program reads that it does not bind: exactly the contract constants
    plus the two wrapper locals. Includes the ABI guard block, which `mainClosed` omits. -/
def progConstNames (pv : PlanView) (m : Model) : List String :=
  (Midfall.LoweringV2.freeNames (abiGuardBlock m ++ mainAsmRaw pv m)).filter
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
  decide (((expectedConsts pv m).map Prod.fst).Nodup) &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x


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

/-- No binder of the program - at ANY depth, `boundSs` - is the name of a contract constant (solc
    rejects it too). This is the hypothesis `inline_append` needs, the object text's `noShadow`, and the
    stricter of the two shadowing scans: `noShadowCore` (§D) checks top-level binders only and is the
    face the registered `prog_slices_decompV3` cites, so `programOkB` carries both and
    `noShadow_of_programOk` projects the second. The B-5 hazard is a model constant named `r`: it is
    substituted at every `mulmod(…, r)` site of a standalone slice and not in the program. -/
def noShadowProg (consts : List (String × Nat)) (prog : YulBlock) : Bool :=
  (Midfall.LoweringV2.boundSs prog).all fun x => !(consts.map Prod.fst).contains x

/- The `noShadow` and `callsResolved` witness/falsifier pair is an EVALUATION, not a `decide`:
    both scans end in `List.contains` on strings, whose `Decidable` instance does not reduce in the
    kernel here. See `Deploy.recon1_scans_ok` - a binder named `FR_MODULUS` (as a `let` and as a
    function parameter) is refused, a plain binder passes; a call to a declared function resolves, an
    undeclared call and a function named after a built-in do not. -/

/-- The builtins whose FIRST argument is the gas the frame hands the callee: the four call ops and
    the two create ops. **D-P71 addition 1 (PG-GAS)** reads "gas() occurs only as the gas argument of
    a call", NOT "no gas()": the external-evaluator render calls the evaluator as
    `staticcall(gas(), …)` (D-P72), so "no gas()" would exclude every external-evaluator render and
    every widened one. TOT.1 needs exactly this fact. -/
def takesGasArg : EVM.Op → Bool
  | .call | .staticcall | .delegatecall | .callcode | .create | .create2 => true
  | _ => false

/-- One layer of the gas scan, in the shape of `noWritersStep` (`Bridge.lean:1069`). A call op skips
    its own `gas()` argument and scans the rest; every other op rejects `gas()` in any position, and
    a `gas()` nested inside a call's OTHER arguments is rejected because that position is not a call
    op's first argument. -/
def gasStep : Scan → (Scan → Bool) → Bool
  | .e (.lit _), _ => true
  | .e (.var _), _ => true
  | .e (.builtin op args), rec =>
      if takesGasArg op then
        match args with
        | Expr.builtin EVM.Op.gas [] :: rest => rec (.es rest)
        | _ => rec (.es args)
      else ! (op == EVM.Op.gas) && rec (.es args)
  | .e (.call _ args), rec => rec (.es args)
  | .es [], _ => true
  | .es (e :: rest), rec => rec (.e e) && rec (.es rest)
  | .s (.block body), rec => rec (.b body)
  | .s (.funDef _ _ _ body), rec => rec (.b body)
  | .s (.letDecl _ none), _ => true
  | .s (.letDecl _ (some e)), rec => rec (.e e)
  | .s (.assign _ e), rec => rec (.e e)
  | .s (.cond c body), rec => rec (.e c) && rec (.b body)
  | .s (.switch c cases dflt), rec =>
      rec (.e c) && rec (.cs cases) &&
        (match dflt with | none => true | some d => rec (.b d))
  | .s (.forLoop init c post body), rec =>
      rec (.b init) && rec (.e c) && rec (.b post) && rec (.b body)
  | .s (.exprStmt e), rec => rec (.e e)
  | .s .break, _ => true
  | .s .continue, _ => true
  | .s .leave, _ => true
  | .b [], _ => true
  | .b (s :: ss), rec => rec (.s s) && rec (.b ss)
  | .cs [], _ => true
  | .cs ((_, b) :: rest), rec => rec (.b b) && rec (.cs rest)

/-- Fuel-bounded gas scan; exhaustion answers `false` (R-37), as `noWritersScan` and `exitScan` do. -/
def gasScan : Nat → Scan → Bool
  | 0, _ => false
  | n + 1, sc => gasStep sc (gasScan n)

/-- **D-P71 addition 1.** Every `gas()` of the block is the gas argument of a call. -/
def GasCallOk (b : Block EVM.Op) : Prop := ∃ n, gasScan n (.b b) = true

/-- WITNESS: a call's own `gas()` passes the scan - the arm that "no gas()" would have excluded, and
    the arm every external-evaluator render lives in. PROVED by `decide`. -/
theorem gasCallOk_witness : GasCallOk (yul% {
    if iszero(staticcall(gas(), 0x0b, 0, 0x100, 0x80, 0x80)) { revert(0, 4) }
    mstore(4096, 1)
    return(4096, 32) }) :=
  ⟨16, by decide⟩

/-- FALSIFIER: the same `gas()` outside a call's gas argument - as a value, as a call's SECOND
    argument, and inside a call's offset argument - is refused at the fuel that accepts the witness;
    zero fuel refuses even the empty block (R-37). PROVED by `decide`. -/
theorem gasCallOk_refuses :
    gasScan 16 (.b (yul% { mstore(0, gas()) })) = false ∧
    gasScan 16 (.b (yul% { pop(gas()) })) = false ∧
    gasScan 16 (.b (yul% { let a := staticcall(0, gas(), 0, 0, 0, 0) })) = false ∧
    gasScan 16 (.b (yul% { let a := staticcall(gas(), 0x0b, gas(), 0, 0, 0) })) = false ∧
    gasScan 0 (.b (yul% { })) = false := by
  decide

/-- Two half-open byte ranges meet. -/
def spansMeet (a b : Nat × Nat) : Bool := !(a.1 + a.2 ≤ b.1 || b.1 + b.2 ≤ a.1)

/-- The bytes the transcript parser writes into memory: every walk window, each base paired with the
    length of the section walked into it (`GenAst.g1WalkLoop` bounds each loop by its section's
    `byteLen`): the six commitment bases, the two single-absorb destinations and the evals run. -/
def walkWindowsOf (pv : PlanView) : List (Nat × Nat) :=
  let M := pv.memory
  let L := pv.proofLayout
  let sum (ss : List ProofSection) : Nat := (ss.map (·.byteLen)).foldl (· + ·) 0
  [ (ptrAddr M.adviceCommsMptrBase, sum L.advicePhases),
    (ptrAddr M.lookupMCommsMptrBase, L.lookupMultiplicities.byteLen),
    (ptrAddr M.permZCommsMptrBase, L.permutationProducts.byteLen),
    (ptrAddr M.lookupHelperCommsMptrBase, sum (L.lookups.map (·.helpers))),
    (ptrAddr M.trashcanCommsMptrBase, L.trash.byteLen),
    (ptrAddr M.quotientLimbCommsMptrBase, L.quotientLimbs.byteLen),
    (ptrAddr M.fComMptr, L.fCom.byteLen),
    (ptrAddr M.piMptr, L.pi.byteLen),
    (ptrAddr M.reversedEvalsMptr, L.evals.byteLen) ]

/-- The longest run of absorbs between two squeezes: one whole section (each walk absorbs its section
    before the squeeze that follows it), or the instance run, absorbed at 128 bytes per instance. -/
def longestAbsorbRunOf (pv : PlanView) (numInstances : Nat) : Nat :=
  let L := pv.proofLayout
  (L.advicePhases.map (·.byteLen) ++
    [L.lookupMultiplicities.byteLen, L.permutationProducts.byteLen, L.trash.byteLen,
      L.quotientLimbs.byteLen, L.evals.byteLen, L.qEvals.byteLen,
      128 * numInstances]).foldl Nat.max 0

/-- **D-P71 addition 2 (PG-TPBUF), stated as a CLAUSE and not as a lemma, and the reason is
    measured: it does NOT follow from `memory.map.WellFormed`.** Two independent reasons, both in the
    tree. (1) `WellFormed` is PHASE-SCOPED: it routes disjointness through `memoryLifetimeIntersects`
    (`Layout.lean:1114-1119`), and gate 14 of `LayoutMemory.lean:884-911` measures FIFTY-FOUR pairs of
    poseidon regions that share bytes under it while the global byte-disjointness predicate on the
    same map is FALSE - so `SupportedV2.layout` cannot give byte-disjointness between the transcript
    region and a walk window. (2) `WellFormed` bounds a region START by `0x80` and checks alignment
    and NOTHING about capacity (gate 15, `LayoutMemory.lean:928-960`: "WellFormed IS strictly weaker
    than `validate`"); the absorb run is a capacity demand. ROW.TP step 3 was to check which - this is
    the check, and the answer is "clause". -/
def transcriptRegionOk (pv : PlanView) (numInstances : Nat) : Bool :=
  match pv.memory.map.region "transcript_buffer" with
  | none => false
  | some t => decide (longestAbsorbRunOf pv numInstances ≤ t.len) &&
      (walkWindowsOf pv).all fun w => !spansMeet (t.start, t.len) w

/-- **D-P71 addition 3 (PG-G1ID).** `EntryFrameV3'` was declined under D-P64, so the only memory the
    frame knows is zero is what `ZeroAbove` gives from `0x80` up: the `g1_identity` window that
    `BaseInv .start` pins to zero has to lie above that floor. A REAL restriction, not a formality:
    the default layout puts `g1IdentityMptr` at 0 (`Layout.lean:1732`). -/
def g1IdentityFloor (pv : PlanView) : Bool := decide (0x80 ≤ ptrAddr pv.memory.g1IdentityMptr)

/-- **D-P71 addition 4 (PG-NEGLAG).** The block reads `l_blind` from word 1 and starts the instance
    walk at `max 2 numNegLagranges` (`GenAst.lean:727-733`), so at `numNegLagranges < 2` it computes
    values the Lean verifier does not. `EnvAgrees.negLagranges` gives
    `numNegLagranges = blindingFactors.toOption.getD 0 + 1`, which is 1 when `blindingFactors` is an
    error - so this does NOT follow from the frozen `EnvAgrees`, and step 4 deletes the
    `WellFormedV3` that did not carry it either. A REAL restriction. -/
def negLagrangesFloor (pv : PlanView) : Bool := decide (2 ≤ pv.numNegLagranges)

/-- The card's clause-2 addition: the calldata length the contract expects fits a word, as a
    computation (the `Prop` face is `EntryFrameV3.cdSize`). -/
def cdBoundB (pv : PlanView) (numInstances : Nat) : Bool :=
  decide (pv.proofLayout.proofEnd + 32 + 32 * numInstances < 2 ^ 256)

/-- The card's clause-2 addition, and the one `SimPins` field that is a program fact: some static
    point set has two points, so the `x = 0` row of the fault table is discharged by a revert in the
    PCS block (Lean and Rust deduplicate opening points BY VALUE, `Kzg/Utils.lean:137`). -/
def hasMultiPointSet (pv : PlanView) : Bool :=
  match Midfall.Generator.intermediateSets pv.meta_ pv.dat with
  | .ok s => (s.pointSets.any fun ps => decide (2 ≤ ps.length))
  | .error _ => false

/-- **D-P59's repaired `WellFormed.permutationCommitmentsMatch`, kept as a computation.** Step 4
    deletes `WellFormedV3`, and `supported` is the FROZEN `SupportedV2`, whose `wf` field still means
    `divCeil columns (csDegree - 2)` - FALSE at the deployment (8 against 3, `Deploy`'s
    `wellFormedPermCounts_ok`) and repaired by R.7. The corrected clause is one sigma commitment per
    permutation COLUMN (`keygen.rs:244-250`, `permutation.rs:123`); it lives here until R.7 merges, at
    which point it is `supported.wf.permutationCommitmentsMatch` and can be dropped from here. -/
def permCommMatchRepaired (vk : VerifyingKey (Fr p) G₁) : Bool :=
  vk.permutation.commitments.size == vk.cs.permutation.columns.size

/-- **ONE BUNDLE FOR THE PROGRAM.** Everything about the emitted program that a computation at a
    render decides: it is the parse of the text (`codegenStruct`, structural) AND the token equality
    the frozen surface states (`codegenAgrees`, the card's "frozen token clause"); its constant table
    is the plan view's (`constsCoherent`); every call resolves; no binder shadows a constant (both the
    object text's every-binder scan and the `noShadowB` face `prog_slices_decompV3` cites); after
    inlining only the wrapper locals are free (`mainClosed`); the transcript base is above Solidity's
    reserved words; and the five D-P71 floors and bounds. -/
def programOkCore (pv : PlanView) (m : Model) (numInstances : Nat)
    (vk : VerifyingKey (Fr p) G₁) : Bool :=
  let main := mainAsmRaw pv m
  let consts := constTableOf m
  codegenStruct main m &&
  codegenAgrees pv m &&
  constsCoherent pv m &&
  callsResolved main &&
  noShadowProg consts (abiGuardBlock m ++ wrapperLocals m 0 0 ++ main) &&
  noShadowCore pv m &&
  mainClosed pv m &&
  decide (0x80 ≤ pv.memory.transcriptMptr) &&
  cdBoundB pv numInstances &&
  hasMultiPointSet pv &&
  transcriptRegionOk pv numInstances &&
  g1IdentityFloor pv &&
  negLagrangesFloor pv &&
  permCommMatchRepaired vk

/-- The render-level face. The fixture render is `noncomputable` (its model is the typed-in artifact
    value), so `Deploy` evaluates `programOkCore` at the render's own computable fields and
    `programOkB_of_valid` is the projection. -/
def programOkB (R : Render p G₁ G₂ Gₜ) : Bool :=
  programOkCore R.pv R.model R.cfg.numInstances R.vk

/-- **THE PROGRAM CLAUSE**: the bundle above plus the TWO SCANS. Both are `∃ n` propositions and stay
    out of the `Bool` so that no fuel is pinned in the statement (section header). ONE exit scan
    (D-P71 addition 5): `ExitDiscipline` is the scan of §I and `ExitShape` below is the SAME
    `exitScan` applied to a different block - there is no second scan function in the tree. -/
def programOk (R : Render p G₁ G₂ Gₜ) : Prop :=
  programOkB R = true ∧ GasCallOk (R.prog 0 0) ∧ ExitDiscipline (R.prog 0 0)

/-- The three names the projections read are in the data table for EVERY plan view and model,
    whatever the four optional arms of the model hold. -/
theorem expectedConsts_lookups (pv : PlanView) (m : Model) :
    (expectedConsts pv m).lookup "FR_MODULUS" = some frModulusConstant ∧
    (expectedConsts pv m).lookup "RETURN_MPTR" = some pv.memory.verifierReturnMptr ∧
    (expectedConsts pv m).lookup "TRANSCRIPT_MPTR" = some pv.memory.transcriptMptr := by
  cases h1 : m.expectedVkCodehash <;> cases h2 : m.quotientExternal <;>
    cases h3 : m.expectedQuotientCodehash <;> cases h4 : m.expectedHasAccumulator <;>
      simp [expectedConsts, h1, h2, h3, h4, List.lookup]

/-- **THE CONSTS-COHERENCE PROJECTION**: the render's table IS the data table, so a lookup in one is
    a lookup in the other. Every table projection below is this lemma plus `expectedConsts_lookups`.
    This is what `GeneratorCertified.lean:458` (`v3_pins_of_valid`) runs on; RECON.1b ports the pin
    bundles through it. -/
theorem lookup_expectedConsts_of_programOkB {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true)
    (name : String) :
    (constTableOf R.model).lookup name = (expectedConsts R.pv R.model).lookup name := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  have hcc := hc.1.1.1.1.1.1.1.1.1.1.1.2
  simp only [constsCoherent, Bool.and_eq_true] at hcc
  rw [eq_of_beq hcc.1.1.2]

/-- **D-P71 addition 6 (PG-FRMOD): NOT a clause.** `FR_MODULUS = p` is `constsCoherent` together with
    `EnvAgrees.modulus`, and here is the proof, so the rows get it as a projection of `hR.program` and
    `hR.env` and the text carries no redundant conjunct. -/
theorem frModulus_of_programOk_of_modulus {R : Render p G₁ G₂ Gₜ}
    (hp : programOkB R = true) (hmod : p = frModulusConstant) :
    R.consts.lookup "FR_MODULUS" = some p := by
  have h : (constTableOf R.model).lookup "FR_MODULUS" = some frModulusConstant := by
    rw [lookup_expectedConsts_of_programOkB hp, (expectedConsts_lookups R.pv R.model).1]
  exact h.trans (congrArg Option.some hmod.symm)

/-- **D-P71 addition 7: NOT a clause either.** `returnMptr` (`Valid.returnMptr`, the clause Q0.5 added
    to the frozen surface) is carried over as a THEOREM of the single text: the table IS
    `expectedConsts`, and `expectedConsts` declares `RETURN_MPTR`. This is the object text's
    `Render.ValidV3.returnMptr_const`, restated for the reconciled clause; the TraceReturn progress
    row reads exactly this. -/
theorem returnMptr_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    ∃ m, R.consts.lookup "RETURN_MPTR" = some m := by
  refine ⟨R.pv.memory.verifierReturnMptr, ?_⟩
  show (constTableOf R.model).lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr
  rw [lookup_expectedConsts_of_programOkB hp, (expectedConsts_lookups R.pv R.model).2.1]

/-- The two D-P71 floors as `Prop`s the rows cite, discharged from the bundle. -/
theorem g1IdentityFloor_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.1.2

theorem negLagranges_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    2 ≤ R.pv.numNegLagranges := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.2

/-- **THE GENERATED-BY CLAUSE** (the object text's `Render.GeneratedBy`, `ObjectV3Full.lean:615`): the
    plan, the compact quotient blocks and the model are what `generateAll` returns for THIS render's
    own verifier-side inputs - including `R.E.delta`, which is how DELTA reaches the program text
    (finding H-7). It replaces the frozen clauses 1-4 (`circuitMeta`, `layout`, `invariants`,
    `model`), the `validate_layout` gap B-7, the VM-lowering gap B+3 and `vkPins.numInst`. -/
def generated (R : Render p G₁ G₂ Gₜ) : Except Fault GenOut :=
  generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags

def GeneratedBy (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ out, generated R = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧ out.model = R.model


/-! ## §V. VALIDITY, V3 - THE SINGLE TEXT (RECON.1)

  ONE structure. The base is the object text's seven clauses (`ObjectV3Full.lean:762-779`); the
  eighteen-clause draft of `StatementsV3.lean:613` is the FALLBACK if D-P67 is struck and stays in the
  evidence directory, not here (the card's Guidance). Where the two texts disagreed:

  * `circuitMeta`, `layout`, `invariants`, `model` (four clauses of the 18-clause text) collapse into
    `generated` - the object text's `GeneratedBy`, which is what the card's step 1 ("take the object
    text's seven-clause structure as the base") means in practice. `PlanMeta` stays defined above
    because `Deploy` and `Falsifiers` measure it; it is no longer a clause.
  * `noShadow`: the object text scans EVERY binder (`boundSs`); the 18-clause text scanned top-level
    binders only (`noShadowCore`). Both are conjuncts of `programOkB` - not a union of two texts but a
    strictness ordering: the every-binder scan is the one `inline_append` needs, and the top-level face
    is the one the registered `prog_slices_decompV3` cites. Neither is dropped; `noShadow_of_programOk`
    projects the second.
  * `exitDiscipline`: kept, as ONE scan, inside `programOk` (addition 5).
  * `cdBound`, `transcriptMptr`, `vkPins`, `vkProgressPins`: the first two are conjuncts of
    `programOkB`; the pin bundles are NOT clauses - `constsCoherent` is, and `vkPins` /
    `vkProgressPins` / `transcriptMptr` are theorems of it (`GeneratorCertified.lean:458` proves the
    bundle; RECON.1b ports it).
  * `payload`: the object text's field list - `digest` in, `delta` out (card step 3).
  * `supported : SupportedV2 R` (frozen), NOT `SupportedV3`: step 4 deletes `SupportedV3` and
    `WellFormedV3`. The repaired permutation clause that `WellFormedV3.wf` carried is kept as
    `permCommMatchRepaired`, a conjunct of `programOkB`, because `SupportedV2` is frozen and cannot
    gain a field; `supported.wf` is refuted at the deployment until R.7 merges and this card reports
    that rather than weakening it. -/

/-- **VALIDITY, V3 - THE ONE TEXT.** Seven clauses in four groups: what the generator produced
    (`generated`, `inputs`), what the program is (`program`, `noWriters`), what the environment and the
    payload say (`env`, `payload`), and the scope (`supported`). Every clause except the five
    codec-bearing fields of `payload` and `SupportedV2.vkPoints` is decided by computation at a
    deployment; the clause table is in `Midfall/Instances/StatementsV3Deploy.lean`. -/
structure ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- G. Plan, compact quotient blocks and model are the generator's output for THIS constraint
      system, configuration, payload and DELTA (the object text's clause 1). -/
  generated : GeneratedBy R
  /-- G. The build inputs are the configuration's and the key's (frozen clause 5, unchanged; the
      18-clause text's `inputs` is verbatim the same). -/
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  /-- P. The program checks: one decidable bundle plus the two scans (D-P71 additions 1-5 and the
      card's four additions, all inside). -/
  program : programOk R
  /-- P. No world write (frozen clause 10, unchanged). -/
  noWriters : NoWriters (R.prog 0 0)
  /-- K. Field, domain and G2 parameters agree (frozen clause 8, unchanged). Carries
      `modulus : p = frModulusConstant`, which with `constsCoherent` is PG-FRMOD (addition 6). -/
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  /-- K. Every payload word is the Lean key's. -/
  payload : PayloadAgrees R
  /-- S. Scope (frozen `SupportedV2`; `wf.permutationCommitmentsMatch` is repaired by R.7 and kept in
      the meantime as `permCommMatchRepaired`). -/
  supported : SupportedV2 R

/-! ### Projections: what the rows and the headline used to read off the eighteen-clause text. -/

theorem programOkB_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : programOkB R = true :=
  hR.program.1

theorem noShadow_of_programOk {R : Render p G₁ G₂ Gₜ} (hp : programOkB R = true) :
    noShadowCore R.pv R.model = true := by
  have hc := hp
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.1.1.1.2

theorem cdBound_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256 := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1.1.1.1.1.2

theorem hasMultiPointSet_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    hasMultiPointSet R.pv = true := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.2

theorem transcriptMptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t := by
  have hc := programOkB_of_valid hR
  simp only [programOkB, programOkCore, Bool.and_eq_true] at hc
  refine ⟨R.pv.memory.transcriptMptr, ?_, of_decide_eq_true hc.1.1.1.1.1.1.2⟩
  show (constTableOf R.model).lookup "TRANSCRIPT_MPTR" = some R.pv.memory.transcriptMptr
  rw [lookup_expectedConsts_of_programOkB (programOkB_of_valid hR),
    (expectedConsts_lookups R.pv R.model).2.2]
theorem frModulus_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    R.consts.lookup "FR_MODULUS" = some p :=
  frModulus_of_programOk_of_modulus (programOkB_of_valid hR) hR.env.modulus

theorem returnMptr_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ∃ m, R.consts.lookup "RETURN_MPTR" = some m :=
  returnMptr_of_programOk (programOkB_of_valid hR)

/-- (`g1IdentityAbove`, §E, is this same inequality stated at the render.) -/
theorem g1IdentityFloor_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    0x80 ≤ ptrAddr R.pv.memory.g1IdentityMptr :=
  g1IdentityFloor_of_programOk (programOkB_of_valid hR)

theorem negLagranges_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    2 ≤ R.pv.numNegLagranges := negLagranges_of_programOk (programOkB_of_valid hR)

theorem exitDiscipline_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) :
    ExitDiscipline (R.prog 0 0) := hR.program.2.2

theorem gasCallOk_of_valid {R : Render p G₁ G₂ Gₜ} (hR : ValidV3 R) : GasCallOk (R.prog 0 0) :=
  hR.program.2.1

/-- **D-P71 addition 5, discharged.** The rows' exit notion (`SoundnessV3`'s `Render.ExitOk`,
    `ExitShape (R.preBlock 0 ++ R.slices6)`) is NOT a second scan: it is the SAME `exitScan` of §I
    applied to a different block, and it is a consequence of the one clause the text carries. The
    block-level half is proved here; the render-level bridge
    (`returnTail? (R.prog 0 0) = some (R.preBlock 0 ++ R.slices6 ++ …)`) is the program decomposition
    `prog_slices_decompV3` already registers as an obligation, and RECON.1b joins the two. -/
def ExitShape (b : Block EVM.Op) : Prop := ∃ n, exitScan n false false (.b b) = true

theorem exitShape_of_exitDiscipline {b : Block EVM.Op} (init : Block EVM.Op)
    (h : ExitDiscipline b) (ht : returnTail? b = some init) : ExitShape init := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by simpa [exitDisciplineFuel, ht] using hn⟩

/-! ## §E. EntryFrameV3 (e)

  OLD (`Statements.lean:240-247`): five fields, no bound on the calldata. `calldatasize` is
  `BitVec.ofNat 256 st.env.calldata.length` (`EVMExec.lean:792`) while `decodeCalldata` compares
  `cd.size` in `Nat` (`Calldata.lean:341`), so `cd ++ (2^256 zero bytes)` runs exactly like `cd`
  and is rejected by Lean: conjunct 1 is false.

  NEW: `cdSize : cd.size < 2 ^ 256`. THE WEAKEST bound that repairs the statement, and a fact
  about every EVM frame (CALLDATASIZE is a word). A tighter "realistic" bound (2^32, the gas
  limit) would shrink the set of covered frames and buy no proof step: every calldata offset the
  program computes is a constant of the render, bounded by `ValidV3.cdBound`. -/

/-- **TRUSTED.** As `LoweringV2.EntryFrame`, plus the calldata length bound. -/
structure EntryFrameV3 (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (st : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    st = { initState W Lyt H cd mem₀ with activeWords := aw }
  zeroAbove : ZeroAbove st.memory
  fmp : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ (loadWord st.memory 0x40).toNat ≤ t
  callvalue : st.env.callvalue = 0
  selector : bytesTake cd 0 4 = some fnSigVerifyProof
  /-- ADDED: the calldata length is a word. -/
  cdSize : cd.size < 2 ^ 256

/-- The V3 frame is a V2 frame: nothing proved from `EntryFrame` is lost. PROVED. -/
theorem EntryFrameV3.toV2 {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrameV3 R W Lyt H cd st) :
    EntryFrame R W Lyt H cd st :=
  ⟨h.shape, h.zeroAbove, h.fmp, h.callvalue, h.selector, h.cdSize⟩

/-- **INHABITATION**, the V3 form of `Blocks.lean:624 entryFrame_inhabited`: one more premise
    (`hcd`), the same witness. PROVED. -/
theorem entryFrame_inhabitedV3 (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (hsel : bytesTake cd 0 4 = some fnSigVerifyProof) (hcv : W.callvalue = 0)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t)
    (hcd : cd.size < 2 ^ 256) :
    ∃ st₀, EntryFrameV3 R W Lyt H cd st₀ := by
  refine ⟨initState W Lyt H cd (fun _ => 0), ⟨fun _ => 0, 0, rfl⟩, ?_, ?_, hcv, hsel, hcd⟩
  · exact fun a _ => rfl
  · obtain ⟨t, ht₁, ht₂⟩ := ht
    refine ⟨t, ht₁, ?_⟩
    have h0 : (loadWord ((initState W Lyt H cd (fun _ : Nat => (0 : UInt8)))).memory 0x40).toNat
        = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; omega

/-- OPTION (finding A-9, a DECISION): zero from the generator's own `TRANSCRIPT_MPTR` up, instead
    of from `0x80`. This is what the on-chain MF-2 guard supports: a fresh frame is zero above
    solc's initial free-memory pointer, the guard enforces `fmp ≤ TRANSCRIPT_MPTR`, and solc may
    have spilled into `[0x80, fmp)`. Strictly weaker than `EntryFrameV3` (lemma below), so it
    covers MORE frames; the price is one decidable pin (`g1IdentityAbove`). -/
structure EntryFrameV3' (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (st : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    st = { initState W Lyt H cd mem₀ with activeWords := aw }
  /-- The free-memory pointer is at or below `TRANSCRIPT_MPTR`, and memory is zero from there. -/
  fmpZero : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧
    (loadWord st.memory 0x40).toNat ≤ t ∧ ∀ a, t ≤ a → st.memory a = 0
  callvalue : st.env.callvalue = 0
  selector : bytesTake cd 0 4 = some fnSigVerifyProof
  cdSize : cd.size < 2 ^ 256

/-- `EntryFrameV3` implies the option when `TRANSCRIPT_MPTR ≥ 0x80` (`Valid.transcriptMptr`).
    PROVED: the option is the weaker assumption. -/
theorem EntryFrameV3.toOption {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrameV3 R W Lyt H cd st)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) :
    EntryFrameV3' R W Lyt H cd st := by
  obtain ⟨t, ht₁, ht₂⟩ := ht
  obtain ⟨t', ht'₁, ht'₂⟩ := h.fmp
  have htt : t' = t := Option.some.inj (ht'₁.symm.trans ht₁)
  subst htt
  exact ⟨h.shape, ⟨t', ht₁, ht'₂, fun a ha => h.zeroAbove a (le_trans ht₂ ha)⟩, h.callvalue,
    h.selector, h.cdSize⟩

/-- The pin the option needs: the `g1_identity` window `Inv` pins to zero at every checkpoint
    lies at or above `TRANSCRIPT_MPTR`. Decidable. -/
def g1IdentityAbove (R : Render p G₁ G₂ Gₜ) : Prop :=
  ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ t ≤ ptrAddr R.pv.memory.g1IdentityMptr

/-! ## §F. Totality (f)

  OLD: none. Conjuncts 1 and 3 of the frozen headline are ∀-runs statements; nothing says the
  modelled program has a run on calldata the Lean verifier rejects.

  WHICH STATEMENT IS THE RIGHT ONE.
  * Gas. `gas()` is the one builtin whose step is `∃ w, g.Gas st w ∧ ...`
    (`EVMExec.lean`, `builtinWithExternal`): under `ExternalGas.none` it is stuck. The supported
    renders never emit `gas()` (trace, gas checkpoints and the external evaluator are excluded by
    `SupportedV3`), so existence holds for every oracle there - but that needs one more scan. The
    statement below asks for a TOTAL oracle instead, which is what a real chain provides and what
    stays true when the scope restrictions are lifted.
  * Calls. `permissive c` admits the failed response to every request (`Bridge.lean:1433
    permissive_failResp_call`). So "a permissive run exists" is witnessed by the run whose FIRST
    precompile call fails and which then reverts through `fail(ERR_PRECOMPILE_FAILED)`: it says
    nothing about the paths on which the precompiles answer. The statement that makes the ∀-runs
    conjuncts non-vacuous on a real chain is existence under the HONEST relation `callsOf product`.
    An honest run is a permissive run (`runBody_mono` below), so the permissive form follows. -/

/-- The gas oracle answers in every state. `ExternalGas.ofFun f` and `ExternalGas.any` are total;
    `ExternalGas.none` is not. -/
def GasTotal (g : ExternalGas) : Prop := ∀ st, ∃ w, g.Gas st w

theorem gasTotal_ofFun (f : EvmState → U256) : GasTotal (ExternalGas.ofFun f) :=
  fun st => ⟨f st, rfl⟩

theorem gasTotal_any : GasTotal ExternalGas.any := fun _ => ⟨0, trivial⟩

theorem not_gasTotal_none : ¬ GasTotal ExternalGas.none := fun h => (h EvmState.init).elim fun _ hw => hw

/-- **TOTALITY.** From every entry frame of a deployed render, under the honest precompiles and
    any total gas oracle, the body has a run - whatever the calldata. -/
def BodyTotal (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (vkAddr : U256)
    (st₀ : EvmState) : Prop :=
  ∀ g : ExternalGas, GasTotal g → ∃ obs, RunBody R vkAddr 0 (callsOf product) g st₀ obs

/-- The honest relation never reports a world change (`ofOutcome`, `failResp`,
    `Bridge.lean:689-696`), so an honest response is a permissive response. PROVED from
    `Bridge.honest_le_permissive`. -/
theorem callsOf_le_permissive (product : PairingProduct) :
    ∀ req st r, (callsOf product).Call req st r → (permissive (callsOf product)).Call req st r := by
  refine honest_le_permissive (callsOf product) ?_
  intro req st r h
  rcases h with h | ⟨_, hF⟩
  · simp only [honestOf, Option.map_eq_some_iff] at h
    obtain ⟨rel, _, hr⟩ := h
    rw [← hr]
    split <;> rfl
  · exact hF.elim

/-- A run under a call relation is a run under any larger one. OBLIGATION (Bridge layer).
    Experiment: induction on `Step`; the call relation occurs only in `externalCall`
    (`EVMExec.lean`), in a positive position. -/
theorem runBody_mono (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256) (c c' : ExternalCalls)
    (g : ExternalGas) (st₀ : EvmState) (obs : Obs)
    (hcc : ∀ req st r, c.Call req st r → c'.Call req st r)
    (h : RunBody R vkAddr qAddr c g st₀ obs) : RunBody R vkAddr qAddr c' g st₀ obs := by
  sorry

/-- CONSEQUENCE, PROVED from `runBody_mono`: totality gives a permissive run, so conjuncts 1 and 3
    are not vacuous at any entry frame. -/
theorem BodyTotal.permissive {R : Render p G₁ G₂ Gₜ} {product : PairingProduct}
    {vkAddr : U256} {st₀ : EvmState}
    (h : BodyTotal R product vkAddr st₀) (g : ExternalGas) (hg : GasTotal g) :
    ∃ obs, RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs := by
  obtain ⟨obs, hobs⟩ := h g hg
  exact ⟨obs, runBody_mono R vkAddr 0 _ _ g st₀ obs (callsOf_le_permissive product) hobs⟩

/-! ## §K. The headline, the gate, end to end (h), (k) -/

/-- `LeanAccepts` is unchanged (`Statements.lean:263-267`). Restated only so that the V3 file
    shows the whole surface; `rfl`. -/
theorem leanAccepts_unchanged (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) :
    LeanAccepts R H cd =
      ∃ ms instW inst,
        decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
        instOfWords? (p := p) instW = some inst ∧
        verifyMsgs (Gₜ := Gₜ) R.E H Features.solidity R.params R.vk inst ms = .ok () := rfl

/-- **LOWERING EQUIVALENCE, V3.** For every world the render is deployed into, every hash, every
    calldata and every entry frame, under honest-or-failing precompiles and a lawful codec:

    1. soundness - a run that returns returns ABI `true`, and the Lean verifier accepts;
    2. completeness - if the Lean verifier accepts, an honest run exists and every honest run
       returns ABI `true` with the world unchanged;
    3. two outcomes - every run returns ABI `true` or is a non-committing halt, world unchanged;
    4. totality - under the honest precompiles and any total gas oracle, a run exists.

    DIFFERENCES FROM `LoweringV2.LoweringEquivalence` (`Statements.lean:298-311`): `EntryFrameV3`
    for `EntryFrame`; the codec laws are a hypothesis of ALL conjuncts (they were a hypothesis of
    conjunct 2 only, and there the frozen seven without the encoder-first law); conjunct 4 is
    new. Conjuncts 1 and 3 are otherwise verbatim. -/
def LoweringEquivalenceV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → obs.isReturn →
        SoundSide R H cd → obs.returnData = abiTrue ∧ LeanAccepts R H cd) ∧
    (LeanAccepts R H cd → CompleteSide R H cd →
        (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀) ∧
    (∀ (g : ExternalGas) (obs : Obs),
        RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs →
        obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀)) ∧
    BodyTotal R product vkAddr st₀

/-- Conjunct 3 is an instance of `TwoOutcomes`. PROVED: no rejection lemma is involved. -/
theorem conj3_of_twoOutcomes (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h : TwoOutcomes R) (vkAddr : U256) (st₀ : EvmState) :
    ∀ (g : ExternalGas) (obs : Obs),
      RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs →
      obs.view = returnView st₀ ∨ (obs.isRevertOrHalt ∧ obs.worldUnchanged st₀) :=
  fun g obs hobs => h vkAddr (permissive (callsOf product)) g st₀ obs hobs

/-! ### The four obligations the headline decomposes into

  The frozen composition (`Blocks.lean:493 lowering_equivalence_of_blocks`) spends the seven
  `BlockSound` rows in conjunct 1 only to read off `returnData = abiTrue`, and closes conjunct 3
  with the false `rejects_of_not_accepts`. With `TwoOutcomes` both uses disappear: -/

/-- PROGRAM-LEVEL REJECTION, V3 (replaces `Blocks.lean:134 Render.Rejects`). `SoundSide` STAYS (it
    excludes the logup-panic set, where the contract accepts and Lean panics). The conclusion is
    `¬ obs.isReturn`; with `TwoOutcomes` that is the same as `obs.isRevertOrHalt`. This is where
    ALL of "the contract returns, so Lean accepts" lives; the staged per-block rejection
    contracts prove it. -/
def RejectsV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    SoundSide R H cd → ¬ LeanAccepts R H cd →
    RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs → ¬ obs.isReturn

/-- Conjunct 2, named. -/
def CompleteV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    LeanAccepts R H cd → CompleteSide R H cd →
      (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
      ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
        obs.view = returnView st₀

/-- Conjunct 4, named. -/
def TotalV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∀ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr → EntryFrameV3 R W Lyt H cd st₀ →
    Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product → G1CodecHeadlineLaws R.E.g1 →
    BodyTotal R product vkAddr st₀

/-- **COMPOSITION, V3.** The headline is four independent obligations: `TwoOutcomes` (syntactic),
    `RejectsV3` (soundness), `CompleteV3` (the progress rows) and `TotalV3` (termination and
    non-stuckness). PROVED, no `sorry`: conjunct 1 is `TwoOutcomes` (a returning run returned
    `abiTrue`) plus `RejectsV3` (and Lean accepted); conjunct 3 is `TwoOutcomes`. -/
theorem lowering_equivalenceV3_of (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h2 : TwoOutcomes R) (hrej : RejectsV3 R product) (hcomp : CompleteV3 R product)
    (htot : TotalV3 R product) : LoweringEquivalenceV3 R product := by
  intro W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec
  refine ⟨?_, hcomp W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec,
    conj3_of_twoOutcomes R product h2 vkAddr st₀,
    htot W Lyt H vkAddr cd st₀ hdep hentry hpc hcodec⟩
  intro g obs hobs hret hside
  constructor
  · rcases h2 vkAddr _ g st₀ obs hobs with hview | ⟨hrh, _⟩
    · have hh : obs.state.halted = some (.ret, abiTrue) := congrArg ObsView.halted hview
      simp only [Obs.returnData, hh]
    · exact absurd hrh (not_isRevertOrHalt_of_isReturn hret)
  · by_contra hna
    exact hrej W Lyt H vkAddr cd st₀ g obs hdep hentry hpc hcodec hside hna hobs hret

/-- `SoundSide` is implied by `LeanAccepts` (the decode is a function, and an accepting
    `verifyMsgs` did not fault in `prepareMsgs`). PROVED: it is listed in the gate below for
    symmetry with conjunct 1, not as an extra demand. -/
theorem soundSide_of_leanAccepts (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : LeanAccepts R H cd) : SoundSide R H cd := by
  obtain ⟨ms, instW, inst, hdec, hinst, hv⟩ := h
  intro ms' instW' inst' hdec' hinst' hpanic
  rw [hdec] at hdec'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hdec')
  rw [hinst] at hinst'
  obtain rfl := Option.some.inj hinst'
  unfold verifyMsgs at hv
  rw [hpanic] at hv
  cases hv

/-- **NON-VACUITY, V3** (replaces `Statements.lean:317-320` and the D-P45 draft). Every hypothesis
    of `LoweringEquivalenceV3` holds at once, AT KECCAK, with a calldata the Lean verifier
    ACCEPTS and the side conditions admit.

    The hash is `keccak256`, not `∃ H`: `DeploymentV2.vkHash` pins `H` at the VK runtime bytes
    only, so an existential hash is met by a hash constant elsewhere, every challenge is then
    independent of the proof, and `π := 1` with a solved-for `fCom` passes `DualMSM.check` for any
    params (finding H+1). `LeanAccepts` is required because without it the gate is satisfied by a
    codec that decodes nothing. `SoundSide` follows from `LeanAccepts` and is kept for symmetry
    with the hypotheses of conjunct 1. -/
def HypothesesInhabitedV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W keccak256 vkAddr ∧ EntryFrameV3 R W Lyt keccak256 cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ G1CodecHeadlineLaws R.E.g1 ∧
      LeanAccepts R keccak256 cd ∧ SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd

/-- What the gate buys, PROVED: at a render where the gate and the headline both hold, an honest
    run exists and returns ABI `true`. So the two together exclude "the contract never returns". -/
theorem returns_of_inhabited (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hEq : LoweringEquivalenceV3 R product) (hI : HypothesesInhabitedV3 R product) :
    ∃ (vkAddr : U256) (st₀ : EvmState) (obs : Obs),
      RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs ∧
        obs.view = returnView st₀ := by
  obtain ⟨W, Lyt, vkAddr, cd, st₀, hdep, hentry, hpc, hcodec, hacc, _, hcomp⟩ := hI
  obtain ⟨_, h2, _, _⟩ := hEq W Lyt keccak256 vkAddr cd st₀ hdep hentry hpc hcodec
  obtain ⟨⟨obs, hobs⟩, hall⟩ := h2 hacc hcomp
  exact ⟨vkAddr, st₀, obs, hobs, hall obs hobs⟩

set_option linter.unusedVariables false in
/-- **END TO END, V3** (replaces `Statements.lean:347-361`). Differences: `ValidV3`,
    `LoweringEquivalenceV3`, `calldataOfV3`, `EntryFrameV3`, and ONE codec hypothesis
    `G1CodecLawsV3` in place of the two frozen ones (`G1CodecLaws` and `compressedRoundtrip`,
    the second of which is a field of the first). -/
def EndToEndV3 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (hR : ValidV3 R)
    (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd) : Prop :=
  verifyNative (Gₜ := Gₜ) R.E Features.solidity R.params R.vk inst π = .ok () ↔
    ∃ cd, calldataOfV3 R π inst = .ok cd ∧
      ∀ st₀, EntryFrameV3 R W Lyt keccak256 cd st₀ →
        (∃ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product) (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀

/-- The size fact `EndToEndV3`'s right-to-left direction needs to build an entry frame for the
    encoder's output: a calldata the decoder accepts has exactly the expected length, which
    `ValidV3.cdBound` bounds. PROVED for the decoder half (`decodeCalldata`'s seventh guard). -/
theorem cdSize_of_decodes {G : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G) (cd : Bytes) (ms : List (Msg (Fr p) G)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd.size = L.proofEnd + 32 + 32 * numInstances := by
  by_contra hne
  have hnone : decodeCalldata (p := p) L numInstances c cd = none := by
    unfold decodeCalldata
    simp [hne]
  rw [hnone] at h
  cases h

/-! ## Axiom audit of what is PROVED here and what rests on a stated obligation -/

#print axioms withCompressed_lawsV3            -- no sorryAx
#print axioms entryFrame_inhabitedV3           -- no sorryAx
#print axioms EntryFrameV3.toOption            -- no sorryAx
#print axioms callsOf_le_permissive            -- no sorryAx
#print axioms lowering_equivalenceV3_of        -- no sorryAx
#print axioms returns_of_inhabited             -- no sorryAx
#print axioms soundSide_of_leanAccepts         -- no sorryAx
#print axioms cdSize_of_decodes                -- no sorryAx
#print axioms fail_lookupV3                    -- no sorryAx
#print axioms hoist_prog_addr_indepV3          -- sorryAx: prog_slices_decompV3
#print axioms twoOutcomes_of_scans             -- sorryAx: twoOutcomes_of_exitDiscipline, scans_prog_addr_indep
#print axioms programOkB_of_valid                -- no sorryAx
#print axioms frModulus_of_valid                 -- no sorryAx
#print axioms returnMptr_of_valid                -- no sorryAx
#print axioms g1IdentityFloor_of_valid           -- no sorryAx
#print axioms negLagranges_of_valid              -- no sorryAx
#print axioms cdBound_of_valid                   -- no sorryAx
#print axioms hasMultiPointSet_of_valid          -- no sorryAx
#print axioms transcriptMptr_of_valid            -- no sorryAx
#print axioms exitShape_of_exitDiscipline        -- no sorryAx
#print axioms gasCallOk_witness                  -- no sorryAx
#print axioms BodyTotal.permissive             -- sorryAx: runBody_mono

end Midfall.LoweringV3

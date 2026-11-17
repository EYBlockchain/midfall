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
    §J  WellFormedV3                       (j)
    §B  PlanMeta (circuitMeta + data)      (b)
    §C  PayloadAgrees                      (c)
    §I  ExitDiscipline, TwoOutcomes        (i)
    §V  SupportedV3, ValidV3
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

/-- The frozen composition, as a function of exactly the three things it reads off the render,
    so that it can be EVALUATED on the in-tree toy data (a `Render` needs a prime-order group and
    a pairing; `CdKats.ToyG` is a two-point type). -/
def frozenCalldataCore {G : Type} (numInstances : Nat) (plan : RepackedProofLayoutPlan)
    (c : G1Codec G) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  (Midfall.Lowering.repackProof (p := p) plan c π).mapError
      Midfall.Generator.GeneratorError.fromRepackError >>= fun π' =>
    Midfall.Lowering.encodeCalldata (p := p) numInstances plan c π' inst

/-- The core IS the frozen `calldataOf`, by `rfl`. -/
theorem frozenCalldataOf_eq_core (R : Render p G₁ G₂ Gₜ) (π : Bytes) (inst : Array (Fr p)) :
    Midfall.LoweringV2.calldataOf R π inst =
      frozenCalldataCore R.cfg.numInstances
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π inst := rfl

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
  (topBinders (abiGuardBlock m ++ wrapperLocals m 0 0 ++ mainAsmRaw pv)).all
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

/-- `VerifyingKey.WellFormed` with the one corrected clause; the other six are verbatim. -/
structure WellFormedV3 (vk : VerifyingKey (Fr p) G₁) (F : Features) : Prop where
  csDegreeMatches : vk.cs.degree = .ok vk.csDegree
  chunkLenPositive : 3 ≤ vk.csDegree
  domainConsistent : vk.domain.n = 2 ^ vk.domain.k ∧
    vk.domain.quotientPolyDegree = vk.csDegree - 1
  /-- One sigma commitment per permutation column (keygen.rs:244-250, permutation.rs:123). -/
  permutationCommitmentsMatch :
    vk.permutation.commitments.size = vk.cs.permutation.columns.size
  fixedCommitmentsMatch : vk.fixedCommitments.size = vk.cs.numFixedColumns
  singlePhase : vk.cs.numChallenges = 0
  committedInstancesOn : F.committedInstances = true

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
  /-- Justifies `let delta := <literal>` in the native permutation block
      (`QuotientNumeratorBlock.yul:1407`, `fr_delta_literal()`): the literal the render carries
      is the canonical value of the `delta` Lean's permutation argument multiplies by. The AST
      emitter for that block (WP-G1) must take its literal from `R.inputs.frDelta`, so that
      `CodegenAgrees` then forces the text's literal to be this one. -/
  delta : R.E.delta.val = Inline.natOfLiteral R.inputs.frDelta

/-- The decidable face of the eight fields that mention no codec and no group element: the header
    scalars, the accumulator quadruple and `delta`. `StatementsV3Deploy.lean` evaluates it. The
    five remaining fields (`g1Base`, `g2Base`, `negSG2`, `fixedComms`, `permutationComms`) compare
    payload bytes with `toEip` of group elements: each needs a codec fact (`toEip` is
    noncomputable at `g1CodecZ`) and, for the three base slots, a pairing whose generators are
    pinned (finding H-2). -/
def payloadScalarsB (PV : PlanView) (numInstances k : Nat) (omega omegaInv : Fr p)
    (rotationLast : Int) (acc : Option Midfall.Generator.AccumulatorEncoding) (delta : Fr p)
    (frDelta : String) : List Bool :=
  let s := vkHeaderTemplateSlotsDefault
  [ payloadWord PV s.numInstances == BitVec.ofNat 256 numInstances,
    payloadWord PV s.k == BitVec.ofNat 256 k,
    payloadWord PV s.nInv == frWord ((((2 ^ k : ℕ) : Fr p))⁻¹),
    payloadWord PV s.omega == frWord omega,
    payloadWord PV s.omegaInv == frWord omegaInv,
    payloadWord PV s.omegaInvToL == frWord (omegaInv ^ rotationLast.natAbs),
    ((payloadWord PV s.hasAccumulator).toNat, (payloadWord PV s.accOffset).toNat,
      (payloadWord PV s.numAccLimbs).toNat, (payloadWord PV s.numAccLimbBits).toNat) ==
        accWordsOfEncoding acc,
    delta.val == Inline.natOfLiteral frDelta ]

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

/-! ## §V. SupportedV3 and ValidV3 -/

/-- `SupportedV2` (`Statements.lean:118-134`) with `wf` stated through `WellFormedV3`. The other
    eleven clauses are verbatim. -/
structure SupportedV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  advice : R.vk.cs.numAdviceColumns ≠ 0
  instShape : R.vk.cs.numInstanceColumns = 2 ∧ R.cfg.numCommittedInstances = 1
  noRotInst : ∀ q ∈ R.vk.cs.instanceQueries.toList, q.2.int = 0
  singlePhase : R.vk.cs.numChallenges = 0
  hLimbs : R.vk.domain.getQuotientPolyDegree = R.vk.csDegree - 1
  vkPoints : ∀ C ∈ R.vk.fixedCommitments.toList ++ R.vk.permutation.commitments.toList,
    ptReadable (R.E.g1.toEip C)
  layout : R.plan.memory.map.WellFormed ∧ R.plan.memory.validate.isOk = true
  production : R.flags.trace = false ∧ R.flags.gasCheckpoints = false
  /-- REPAIRED (j). -/
  wf : WellFormedV3 R.vk Features.solidity
  noAcc : R.cfg.accumulator = none
  embeddedQuotient : R.flags.externalQuotient = false ∧ R.flags.expectedQuotient = none
  separateVk : R.flags.separate = true

/-- VALIDITY, V3. Eighteen clauses: the thirteen of `LoweringV2.Render.Valid`
    (`Statements.lean:182-217`) with two repaired (`circuitMeta`, `supported`), and five added
    (`payload`, `exitDiscipline`, `noShadow`, `cdBound`, and the `Data` half of `circuitMeta`,
    which is inside `PlanMeta`). Every clause except the five codec-bearing fields of `payload`
    and `SupportedV3.vkPoints` is decided by computation at a deployment. -/
structure ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  /-- REPAIRED (b): the plan's meta is the raw meta post-processed the way `vk.rs:504-519` does,
      and the plan's data is `Data.new` of it. -/
  circuitMeta : PlanMeta R
  /-- Unchanged text; satisfiable together with clause 1 now. -/
  layout : ProofCalldataLayout.fromProtocol R.plan.meta_.protocol abiVerifyProofProofCptr
      R.plan.meta_.numEvals R.plan.meta_.numPointSets = .ok R.plan.proofLayout
  invariants : R.plan.validateGeneratorInvariants = .ok (.ok ())
  model : generateVerifierFromPlan (fun _ _ => R.qblocks) R.inputs R.flags R.plan = .ok R.model
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧
    R.inputs.accEncoding = R.cfg.accumulator ∧ R.inputs.k = R.vk.domain.k ∧
    R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  codegen : CodegenAgrees R.pv R.model
  closed : mainClosed R.pv R.model = true
  slots : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  /-- ADDED (c): the payload words and the emitted `delta` literal are the Lean key's. -/
  payload : PayloadAgrees R
  /-- REPAIRED (j) through `SupportedV3.wf`. -/
  supported : SupportedV3 R
  noWriters : NoWriters (R.prog 0 0)
  /-- ADDED (i): the only committing exit is the final `return` of the word 1. -/
  exitDiscipline : ExitDiscipline (R.prog 0 0)
  /-- ADDED (d): no top-level binder is a constant name. -/
  noShadow : noShadowB R = true
  /-- ADDED (e): the calldata length the contract expects fits a word, so the contract's
      `calldatasize` comparison and `decodeCalldata`'s `Nat` comparison (`Calldata.lean:341`)
      are the same test. -/
  cdBound : R.plan.proofLayout.proofEnd + 32 + 32 * R.cfg.numInstances < 2 ^ 256
  transcriptMptr : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t
  vkPins : vkPins R
  vkProgressPins : vkProgressPins R

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
  ⟨h.shape, h.zeroAbove, h.fmp, h.callvalue, h.selector⟩

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
#print axioms BodyTotal.permissive             -- sorryAx: runBody_mono

end Midfall.LoweringV3

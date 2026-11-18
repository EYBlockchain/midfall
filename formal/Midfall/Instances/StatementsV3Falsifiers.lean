/-
  StatementsV3Falsifiers (SCRATCH - design area "statements", PLAN-V3)

  CHEAP MACHINE CHECKS THAT THE BROKEN STATEMENTS ARE BROKEN. Every `theorem` and `example` here
  is PROVED (no `sorry` in this file). Every measurement below is a `*_ok : Bool` gate that
  compares the WHOLE measured value to the literal ST.1 printed and is annotated
  `#eval ... -- expect true` (ST.1b: a tuple or string print cannot carry an expectation, because
  scripts/kat_gate.py:40 reads one as [^\s,]+). Section
  F9 deliberately CITES the tree's sorried `rejects_of_not_accepts` to derive `False` from it, so
  its `#print axioms` shows `sorryAx` - that is the finding, not a hole of this file.

    F1  the frozen `calldataOf` repacks twice                       (Statements.lean:335-340)
    F2  the frozen `circuitMeta` forces `numPointSets = 0`          (Statements.lean:186-190)
    F3  `calldatasize` wraps, `decodeCalldata` does not             (Statements.lean §3, the
        pre-ST.4 frame pinned here as `EntryFramePreST4`; the live frame now refuses it)
    F4  `EnvAgrees` pins neither `delta` nor any commitment         (Inv.lean:533-579)
    F5  the frozen seven codec laws hold at a codec that decodes nothing
    F6  `[hoist (R.prog 0 0)]` breaks `fail_lookup := rfl`
    F7  `WellFormed.permutationCommitmentsMatch` at the deployment
    F8  the frozen gate does not ask for `LeanAccepts`
    F9  `rejects_of_not_accepts` contradicts any accepted calldata with a returning run
-/
import Midfall.LoweringV3.Statements
import Midfall.Instances.PoseidonValid
import Midfall.Instances.CurveSurface
set_option autoImplicit false

namespace Midfall.LoweringV3.Falsifiers

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.Assumptions
open YulSemantics YulSemantics.EVM Midfall.Yul Midfall.Yul.Bridge
open Midfall.LoweringV2 Midfall.LoweringV3

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ## F1. The double repack -/

section F1
open Midfall.Lowering.CdKats
local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

-- the frozen composition on the toy proof: not `.ok`
#eval frozenCalldata_isOk -- expect false
-- the repaired composition on the same proof: `.ok`, and it decodes back
#eval calldataOfV3_witness_ok -- expect true

-- WHY: the first repack returns `repackedLen` bytes; the second demands `compressedLen`
/-- The first repack returns 416 bytes - the plan's repackedLen - while the plan's compressedLen is
    176: (416, 416, 176). Gated as a Bool because a tuple print cannot carry an expectation. -/
def firstRepackLengths_ok : Bool :=
  (match Midfall.Lowering.repackProof (p := 17) katPlan toyCodec katCompressed with
     | .ok out => (out.size, katPlan.repackedLen, katPlan.compressedLen)
     | .error _ => (0, 0, 0)) == (416, 416, 176)
#eval firstRepackLengths_ok -- expect true

-- and the second repack, alone, on the first one's output
/-- ... and the second repack, alone, on the first one's output, fails with EXACTLY
    "lengthMismatch expected 176 actual 416" - the two lengths the frozen composition confuses. The
    string contains a space, so the gate is the Bool that pins the whole string, not a print of it. -/
def secondRepackError_ok : Bool :=
  (match Midfall.Lowering.repackProof (p := 17) katPlan toyCodec katCompressed with
     | .ok out => (match Midfall.Lowering.repackProof (p := 17) katPlan toyCodec out with
                   | .ok _ => "ok"
                   | .error (RepackError.lengthMismatch e a _ _ _) =>
                       s!"lengthMismatch expected {e} actual {a}"
                   | .error _ => "other error")
     | .error _ => "first repack failed") == "lengthMismatch expected 176 actual 416"
#eval secondRepackError_ok -- expect true

end F1

section F1deploy
open Midfall.Instances Midfall.Instances.PoseidonInputs

-- the same two lengths at the deployment's layout: the Rust proof is 2640 bytes, the repacked
-- proof 4320, so the frozen `calldataOf` throws lengthMismatch(2640, 4320) for every proof
/-- The same two lengths at the deployment's layout: (2640, 4320, 4320). The Rust proof is 2640 bytes,
    the repacked proof 4320, so the frozen calldataOf throws lengthMismatch(2640, 4320) for EVERY
    proof at the deployment, not only for the toy one. -/
def deployRepackLengths_ok : Bool :=
  ((RepackedProofLayoutPlan.fromProofLayout poseidonPlanV2.proofLayout).compressedLen,
     (RepackedProofLayoutPlan.fromProofLayout poseidonPlanV2.proofLayout).repackedLen,
     poseidonPlanV2.proofLayout.proofLen) == (2640, 4320, 4320)
#eval deployRepackLengths_ok -- expect true

end F1deploy

/-! ## F2. The frozen clause 1 forces a zero point-set count, for EVERY render -/

/-- `ConstraintSystemMeta.new` never returns a non-zero `numPointSets` (`Encoding.lean:473`). -/
theorem new_numPointSets_zero {F : Type} (feat : Features) (cs : ConstraintSystem F) (n : Nat)
    (m : ConstraintSystemMeta) (h : ConstraintSystemMeta.new feat cs n = .ok m) :
    m.numPointSets = 0 := by
  unfold ConstraintSystemMeta.new at h
  cases hp : ProtocolPlan.fromConstraintSystem feat cs n with
  | error e =>
      rw [hp] at h
      cases h
  | ok pr =>
      rw [hp] at h
      have h' := Except.ok.inj h
      rw [← h']

/-- So every render satisfying the FROZEN clause 1 has a plan meta with zero point sets - and by
    the frozen `layout` clause a proof layout with no `q_eval` words. Rust's plan has
    `kzg::num_point_sets` of them (3 at the deployment).

    ST.6 (D-P67) cut the frozen `Render.Valid` over to the seven V3 clauses, and `circuitMeta` is
    not one of them: it collapsed into `generated`. F2 is a falsifier of the OLD text, so the old
    clause is PINNED here, verbatim, as a Prop copy - the same move ST.4 made with `EntryFramePreST4`
    and `frozenCalldataCore` when ST.4 retired the text they falsified. What F2 says is unchanged:
    a render whose plan meta is what `ConstraintSystemMeta.new` returns has zero point sets, and no
    faithful plan does. -/
def ValidPreST6_circuitMeta (R : Render p G₁ G₂ Gₜ) : Prop :=
  ConstraintSystemMeta.new Features.solidity R.vk.cs R.cfg.numCommittedInstances = .ok R.plan.meta_

/-- The frozen `layout` clause, likewise pinned: `ProofCalldataLayout.fromProtocol` on a meta whose
    `numPointSets` is the raw zero derives a layout with no `q_eval` words. -/
def ValidPreST6_layout (R : Render p G₁ G₂ Gₜ) : Prop :=
  ProofCalldataLayout.fromProtocol R.plan.meta_.protocol abiVerifyProofProofCptr
    R.plan.meta_.numEvals R.plan.meta_.numPointSets = .ok R.plan.proofLayout

theorem frozenValid_numPointSets_zero (R : Render p G₁ G₂ Gₜ)
    (h : ValidPreST6_circuitMeta R) :
    R.plan.meta_.numPointSets = 0 :=
  new_numPointSets_zero _ _ _ _ h

/-- While the V3 clause gives the generator's count. -/
theorem planMeta_numPointSets (R : Render p G₁ G₂ Gₜ) (h : PlanMeta R) :
    numPointSets (R.plan.meta_.setNumPointSets 0) R.plan.data = .ok R.plan.meta_.numPointSets := by
  obtain ⟨m0, n, hnew, _, hn, hmeta⟩ := h
  have h0 : m0.numPointSets = 0 := new_numPointSets_zero _ _ _ _ hnew
  have hback : R.plan.meta_.setNumPointSets 0 = m0.setNumDummyEvals 0 := by
    rw [hmeta]
    cases m0
    simp_all [ConstraintSystemMeta.setNumPointSets, ConstraintSystemMeta.setNumDummyEvals]
  rw [hback, hn, hmeta]
  rfl

section F2deploy
open Midfall.Instances Midfall.Instances.PoseidonEnv Midfall.Instances.PoseidonInputs

-- the deployment: (frozen clause 1, layout clause, derived proofLen, deployed proofLen, numPointSets
-- the generator computes from the plan's own data)
/-- The deployment: (true, false, 4224, 4320, 3) = frozen clause 1, the layout clause, the derived
    proofLen, the deployed proofLen, and the count the GENERATOR computes from the plan's own data.
    Clause 1 holds precisely because the plan's meta is the raw one, and that is what makes the derived
    length 4224 instead of 4320 - while numPointSets says 3. -/
def f2DeployMeasurement_ok : Bool :=
  (frozenCircuitMetaB poseidonVkExec.cs 1 poseidonPlanV2, planLayoutB poseidonPlanV2,
    (match ProofCalldataLayout.fromProtocol poseidonPlanV2.meta_.protocol abiVerifyProofProofCptr
        poseidonPlanV2.meta_.numEvals poseidonPlanV2.meta_.numPointSets with
      | .ok l => l.proofLen | .error _ => 0),
    poseidonPlanV2.proofLayout.proofLen,
    (match numPointSets poseidonPlanV2.meta_ poseidonPlanV2.data with | .ok n => n | .error _ => 999)) ==
    (true, false, 4224, 4320, 3)
#eval f2DeployMeasurement_ok -- expect true

end F2deploy

/-! ## F3. `calldatasize` is a word; `decodeCalldata` compares lengths in `Nat` -/

/-- `cd` followed by `N` zero bytes. -/
def padBytes (cd : Bytes) (N : Nat) : Bytes := ⟨cd.data ++ Array.replicate N 0⟩

theorem padBytes_size (cd : Bytes) (N : Nat) : (padBytes cd N).size = cd.size + N := by
  show (cd.data ++ Array.replicate N (0 : UInt8)).size = cd.data.size + N
  rw [Array.size_append, Array.size_replicate]

theorem padBytes_toList (cd : Bytes) (N : Nat) :
    (padBytes cd N).data.toList = cd.data.toList ++ List.replicate N 0 := by
  show (cd.data ++ Array.replicate N (0 : UInt8)).toList = _
  rw [Array.toList_append, Array.toList_replicate]

/-- THE WRAP: the word `calldatasize` returns (`EVMExec.lean:792`) is the same for a calldata
    and for that calldata followed by `2^256` zero bytes. -/
theorem calldatasize_word_wraps (l : List UInt8) :
    BitVec.ofNat 256 (l ++ List.replicate (2 ^ 256) (0 : UInt8)).length =
      BitVec.ofNat 256 l.length := by
  -- no `simp` here: its `List.replicate` simproc would unfold 2^256 elements
  rw [List.length_append, List.length_replicate]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_mod_right]

/-- It is that word the builtin returns. -/
example (st : EvmState) :
    EVM.stepOp EVM.Op.calldatasize [] st =
      some (.ok [BitVec.ofNat 256 st.env.calldata.length] st) := rfl

/-- Every calldata READ is blind to the padding too: `calldataload` and `calldatacopy` go through
    `byteFrom`, which already pads with zeros (`EVMExec.lean:329`). -/
theorem byteFrom_pad (l : List UInt8) (N i : Nat) :
    EVM.byteFrom (l ++ List.replicate N (0 : UInt8)) i = EVM.byteFrom l i := by
  unfold EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hi : i < l.length
  · rw [List.getElem?_append_left hi]
  · have hi' : l.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hi', List.getElem?_replicate, List.getElem?_eq_none hi']
    split <;> rfl

theorem wordFrom_pad (l : List UInt8) (N q : Nat) :
    EVM.wordFrom (l ++ List.replicate N (0 : UInt8)) q = EVM.wordFrom l q := by
  unfold EVM.wordFrom
  simp only [byteFrom_pad]

/-- While the Lean decoder accepts at most one of the two: an accepted calldata has EXACTLY the
    expected length (`decodeCalldata`'s seventh guard, `Calldata.lean:341`). -/
theorem leanAccepts_pad_false (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) (N : Nat)
    (hN : 0 < N) (h : LeanAccepts R H cd) : ¬ LeanAccepts R H (padBytes cd N) := by
  obtain ⟨ms, instW, _, hdec, _, _⟩ := h
  rintro ⟨ms', instW', _, hdec', _, _⟩
  have h1 := cdSize_of_decodes _ _ _ _ _ _ hdec
  have h2 := cdSize_of_decodes _ _ _ _ _ _ hdec'
  rw [padBytes_size] at h2
  omega

/-- THE PRE-ST.4 TEXT OF `LoweringV2.EntryFrame`, PINNED VERBATIM (the D-P27 pattern: an amended
    frozen statement keeps its old text as a named proposition next to the exhibit that shows why
    it was wrong). ST.4 added the sixth field `cdSize`, which is exactly what F3 is about: the five
    fields below admit the padded calldata, the live six refuse it. The proof below is the
    pre-ST.4 proof of `Blocks.lean`'s `entryFrame_inhabited`, verbatim, at the padded calldata. -/
structure EntryFramePreST4 (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash)
    (cd : Bytes) (st : EvmState) : Prop where
  shape : ∃ (mem₀ : Nat → UInt8) (aw : U256),
    st = { Midfall.LoweringV2.initState W Lyt H cd mem₀ with activeWords := aw }
  zeroAbove : Midfall.LoweringV2.ZeroAbove st.memory
  fmp : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ (loadWord st.memory 0x40).toNat ≤ t
  callvalue : st.env.callvalue = 0
  selector : bytesTake cd 0 4 = some fnSigVerifyProof

/-- And the FROZEN frame - the pinned five-field text above - admits the padded calldata whenever
    it admits the original (the selector is the first four bytes): nothing in it excludes the
    padding. Against the live frame the same statement is FALSE, which is the repair. -/
theorem entryFrame_inhabited_padded (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout)
    (H : Hash) (cd : Bytes) (N : Nat)
    (hsel : bytesTake (padBytes cd N) 0 4 = some fnSigVerifyProof) (hcv : W.callvalue = 0)
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t) :
    ∃ st₀, EntryFramePreST4 R W Lyt H (padBytes cd N) st₀ := by
  refine ⟨Midfall.LoweringV2.initState W Lyt H (padBytes cd N) (fun _ => 0),
    ⟨fun _ => 0, 0, rfl⟩, ?_, ?_, hcv, hsel⟩
  · exact fun a _ => rfl
  · obtain ⟨t, ht₁, ht₂⟩ := ht
    refine ⟨t, ht₁, ?_⟩
    have h0 :
        (loadWord ((Midfall.LoweringV2.initState W Lyt H (padBytes cd N)
          (fun _ : Nat => (0 : UInt8)))).memory 0x40).toNat = 0 := by
      show (loadWord (fun _ : Nat => (0 : UInt8)) 0x40).toNat = 0
      decide
    rw [h0]; omega

/-- The V3 frame refuses it: the bound is exactly what separates the two. -/
theorem entryFrameV3_refuses_padded (R : Render p G₁ G₂ Gₜ) (W : ExecEnv) (Lyt : EVM.Layout)
    (H : Hash) (cd : Bytes) (st : EvmState) :
    ¬ EntryFrameV3 R W Lyt H (padBytes cd (2 ^ 256)) st := by
  intro h
  have := h.cdSize
  rw [padBytes_size] at this
  omega

/-! ## F4. `EnvAgrees` (the only payload-to-key clause of the frozen `Valid`) is blind to `delta`
    and to every commitment -/

/-- Any `delta` at all. -/
theorem envAgrees_delta_free {E : VerifierEnv p G₁ G₂ Gₜ} {vk : VerifyingKey (Fr p) G₁}
    {PV : PlanView} {params : ParamsVerifierKZG G₁ G₂} {sG2gen : G₂}
    (h : EnvAgrees E vk PV params sG2gen) (d : Fr p) :
    EnvAgrees { E with delta := d } vk PV params sG2gen :=
  ⟨h.modulus, h.truncWidth, h.domainN, h.baryWeight, h.omegaInvMul, h.omegaOrder, h.negLagranges,
    h.nG2, h.sG2, h.vkDigestWord⟩

/-- Any fixed and permutation commitments at all. -/
theorem envAgrees_commitments_free {E : VerifierEnv p G₁ G₂ Gₜ} {vk : VerifyingKey (Fr p) G₁}
    {PV : PlanView} {params : ParamsVerifierKZG G₁ G₂} {sG2gen : G₂}
    (h : EnvAgrees E vk PV params sG2gen) (fc pc : Array G₁) :
    EnvAgrees E { vk with fixedCommitments := fc, permutation := { commitments := pc } } PV params
      sG2gen :=
  ⟨h.modulus, h.truncWidth, h.domainN, h.baryWeight, h.omegaInvMul, h.omegaOrder, h.negLagranges,
    h.nG2, h.sG2, h.vkDigestWord⟩

/- **`PayloadAgrees` IS BLIND TO `delta` NOW, ON PURPOSE (RECON.1 step 3).** The 18-clause text had
   a `delta` field and this file proved `payloadAgrees_pins_delta` from it: two renders differing
   only in `E.delta` could not both satisfy `PayloadAgrees`. The single text drops that field because
   the `generated` clause pins `E.delta` against the PROGRAM instead - OBJ.7's gate 9
   (`GeneratedKats.generateAll_falsifierDeltaAndOmega_ok`) measures that `delta := 2` changes the
   generated text AND the quotient blocks, while gate 9's second half measures that flipping a
   payload word does NOT make the generator refuse, which is why `PayloadAgrees` is still needed
   alongside `generated`. The card's acceptance line - "`delta := 2` falsifies `generated` (not
   `payload`)" - is exactly this swap, so the old theorem is deleted rather than restated. -/

/-! ## F5. The frozen codec bundle is met by a codec that decodes nothing -/

section F5
open Midfall.Instances

example : G1CodecLaws g1CodecZ := Midfall.Instances.CurveSurface.g1CodecZ_laws
example : ∀ b : Bytes, g1CodecZ.ofCompressed? b = none := fun _ => rfl
example : Midfall.Instances.PoseidonV2.poseidonRender.E.g1 = g1CodecZ := rfl

/-- So the one G1 read every proof starts with fails, at any transcript. -/
example (t : Transcript) :
    ¬ ∃ r, Transcript.read (hashableG1 g1CodecZ) t = .ok r := by
  rintro ⟨r, hr⟩
  unfold Transcript.read at hr
  cases hb : bytesTake t.buffer t.pos (hashableG1 g1CodecZ).width with
  | none => rw [hb] at hr; cases hr
  | some repr =>
      rw [hb] at hr
      have hn : (hashableG1 g1CodecZ).readRepr? repr = none := rfl
      simp only [hn] at hr
      cases hr

end F5

/-! ## F6. The two candidate scopes -/

/-- Candidate A of §D: the hoist of the whole closed program. -/
def scopeA (R : Render p G₁ G₂ Gₜ) (c : ExternalCalls) (g : ExternalGas) :
    FunEnv (Bridge.Dialect c g) := [hoist (Bridge.Dialect c g) (R.prog 0 0)]

set_option linter.unusedVariables false in
/-- `fail_lookup` (`Blocks/TraceReturn.lean:405`) is `rfl` at the frozen scope and at `scopeV3`
    (`fail_lookupV3`), and is NOT `rfl` at candidate A. -/
example (R : Render p G₁ G₂ Gₜ) {c : ExternalCalls} {g : ExternalGas} : True := by
  fail_if_success
    have : lookupFun (scopeA R c g) "fail" =
      some ({ params := ["sel"], rets := [],
              body := [Stmt.exprStmt (Expr.builtin EVM.Op.mstore
                  [Expr.lit (.number 0),
                   Expr.builtin EVM.Op.shl [Expr.lit (.number 224), Expr.var "sel"]]),
                Stmt.exprStmt (Expr.builtin EVM.Op.revert
                  [Expr.lit (.number 0), Expr.lit (.number 4)])] },
            scopeA R c g) := rfl
  trivial

/-! ## F7. `WellFormed.permutationCommitmentsMatch` at the deployment -/

section F7
open Midfall.Instances Midfall.Instances.PoseidonEnv

-- (sigma commitments in the VK, permutation columns, the frozen clause's right-hand side)
/-- (8, 8, 3): sigma commitments in the VK, permutation columns, and the frozen clause's right-hand
    side. The corrected clause (8 = 8) holds; the frozen divCeil one does not. Gated as a Bool: a
    tuple print carries no expectation. -/
def f7WellFormedCounts_ok : Bool :=
  (poseidonVkExec.permutation.commitments.size, poseidonVkExec.cs.permutation.columns.size,
    divCeil poseidonVkExec.cs.permutation.columns.size (poseidonVkExec.csDegree - 2)) == (8, 8, 3)
#eval f7WellFormedCounts_ok -- expect true

end F7

/-! ## F8. The frozen gate is implied by a statement with no accepted calldata in it -/

/-- `HypothesesInhabited` (`Statements.lean:317-320`) asks for `SoundSide` and `CompleteSide`
    only. Both are implications from a successful decode, so they hold at every calldata that
    does NOT decode: the frozen gate can be met with a calldata the verifier rejects. -/
theorem frozenSides_of_not_decodes (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (hnd : decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = none) :
    SoundSide R H cd ∧ CompleteSide R H cd ∧ ¬ LeanAccepts R H cd := by
  refine ⟨?_, ?_, ?_⟩
  · intro ms instW inst hdec
    rw [hnd] at hdec
    cases hdec
  · intro ms instW inst Snap hdec
    rw [hnd] at hdec
    cases hdec
  · rintro ⟨ms, instW, inst, hdec, _⟩
    rw [hnd] at hdec
    cases hdec

/-! ## F9. `rejects_of_not_accepts` is inconsistent with the goal of the project -/

/-- The render with one more public instance configured. Its program, constant table and runs
    are those of `R` by `rfl`; its deployment predicate and entry frame are those of `R` field by
    field; its codec and `encG2` are `R`'s by projection. -/
def bumpInst (R : Render p G₁ G₂ Gₜ) : Render p G₁ G₂ Gₜ :=
  { R with cfg := { R.cfg with numInstances := R.cfg.numInstances + 1 } }

example (R : Render p G₁ G₂ Gₜ) (a b : U256) : (bumpInst R).prog a b = R.prog a b := rfl
example (R : Render p G₁ G₂ Gₜ) : (bumpInst R).consts = R.consts := rfl
example (R : Render p G₁ G₂ Gₜ) (a b : U256) (c : ExternalCalls) (g : ExternalGas)
    (st : EvmState) (obs : Obs) : RunBody (bumpInst R) a b c g st obs = RunBody R a b c g st obs :=
  rfl

/-- The deployment predicate transfers field by field: no field reads `cfg.numInstances`. -/
theorem deployment_bump {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {H : Hash} {a : U256}
    (h : DeploymentV2 R W H a) : DeploymentV2 (bumpInst R) W H a :=
  ⟨h.keccak, h.wf, h.vkCode, h.vkHash, h.vkNonEmpty, h.disjoint⟩

/-- So does the entry frame. -/
theorem entryFrame_bump {R : Render p G₁ G₂ Gₜ} {W : ExecEnv} {Lyt : EVM.Layout} {H : Hash}
    {cd : Bytes} {st : EvmState} (h : EntryFrame R W Lyt H cd st) :
    EntryFrame (bumpInst R) W Lyt H cd st :=
  ⟨h.shape, h.zeroAbove, h.fmp, h.callvalue, h.selector, h.cdSize⟩

/-- But the Lean verifier of the bumped render rejects everything `R` accepts: the expected
    calldata length moved by 32. -/
theorem leanAccepts_bump_false (R : Render p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : LeanAccepts R H cd) : ¬ LeanAccepts (bumpInst R) H cd := by
  obtain ⟨ms, instW, _, hdec, _, _⟩ := h
  rintro ⟨ms', instW', _, hdec', _, _⟩
  have h1 := cdSize_of_decodes _ _ _ _ _ _ hdec
  have h2 := cdSize_of_decodes _ _ _ _ _ _ hdec'
  have h3 : (bumpInst R).cfg.numInstances = R.cfg.numInstances + 1 := rfl
  have h4 : (bumpInst R).plan.proofLayout = R.plan.proofLayout := rfl
  rw [h3, h4] at h2
  omega

/-- **THE REFUTATION.** The tree's sorried `rejects_of_not_accepts` (`Blocks.lean:356`) and ONE
    accepted calldata with a returning permissive run - at any render whatever - give `False`.
    Such a calldata is what conjunct 2 of the headline promises at every render the gate is
    proved for. The statement lacks `R.Valid`, which is all this uses; `SoundSide` is a second,
    independent defect. -/
theorem rejects_of_not_accepts_contradiction (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState)
    (g : ExternalGas) (obs : Obs)
    (hdep : DeploymentV2 R W H vkAddr) (hentry : EntryFrame R W Lyt H cd st₀)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hacc : LeanAccepts R H cd)
    (hobs : RunBody R vkAddr 0 (permissive (callsOf product)) g st₀ obs)
    (hret : obs.isReturn) : False :=
  not_isRevertOrHalt_of_isReturn hret
    (rejects_of_not_accepts (bumpInst R) product W Lyt H vkAddr cd st₀ g obs (deployment_bump hdep)
      (entryFrame_bump hentry) hpc (leanAccepts_bump_false R H cd hacc) hobs)

#print axioms new_numPointSets_zero
#print axioms frozenValid_numPointSets_zero
#print axioms leanAccepts_pad_false
#print axioms entryFrameV3_refuses_padded
#print axioms envAgrees_delta_free
#print axioms leanAccepts_bump_false
#print axioms rejects_of_not_accepts_contradiction

end Midfall.LoweringV3.Falsifiers

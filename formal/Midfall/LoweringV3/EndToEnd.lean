/-
  Midfall.LoweringV3.EndToEnd

  WP D1 / PL.E - the end-to-end theorem `EndToEndV3`.

  THE ONE EXTERNAL FACT. `EndToEndV3`'s left-to-right direction needs the
  read-schedule agreement `readScheduleAgrees` of `Lowering/Obligations.lean:443`
  for the render's OWN key and layout: every message list the Rust-faithful decoder
  `decodeRust` returns has the slot shape of `R.plan.proofLayout`. That is the
  hypothesis `hsched` below. It is the V3 form of `Obligations.readScheduleAgrees`
  (where it is a field of `LoweringCorrect`), and it is exactly what
  `repack_spec_of_decodeRust` (`Lowering/Calldata.lean:1276`) takes.

  Everything else is the tree's proved glue. The arm lemma is stated with `hsched`
  explicit so the missing V3 projection is one named goal, not a hole in the
  theorem's proof.

  THE EXACT REMAINING GOAL, for the next worker:

      theorem readScheduleAgrees_of_validV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
        ∀ (inst : Array (Fr p)) (π : Bytes) (ms : List (Msg (Fr p) G₁)),
          decodeRust (Gₜ := Gₜ) R.E Features.solidity R.vk inst π = some ms →
            ms.map Msg.slot =
              (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots

  This is `Obligations.readScheduleAgrees` specialised to `ValidV3`. The v1 field
  is REFUTED at the deployment because `Surface.vk` and `Surface.plan` were free
  fields (`Instances/ObligationsGates.lean:890`); V3's `generated` is the new pin
  (the layout is built by `newFromVk` from `ConstraintSystemMeta.new` on
  `R.vk.cs`), but no projection theorem turns that construction into the read
  order of `Verifier.prepare`. It is a new verifier-vs-protocol refinement, not a
  hypothesis to add to `ValidV3`: `end_to_end_of_readSchedule` below is the exact
  target with this one premise.
-/
import Midfall.LoweringV3.Composition
import Midfall.LoweringV3.PrefixV3
import Midfall.Lowering.Obligations
import Midfall.Tools.ConeSorries
import Midfall.Tools.Done

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

/-! ## 1. The layout statics `EndToEndV3` needs from `ValidV3` -/

/-- `ValidV3` gives `proofLen = repackedLen` for the render's own layout. The proof is
    `layout_static_of_generated`'s peel with the first conjunct of
    `proofLen_eq_repackedLen` kept instead of the second. PROVED. -/
theorem proofLen_eq_repackedLen_of_validV3 (R : Render p G₁ G₂ Gₜ) (hR : ValidV3 R) :
    R.plan.proofLayout.proofLen =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).repackedLen := by
  obtain ⟨rawMeta, plan, _hraw, hpl, hp⟩ := pfx_plan_of_generated hR.generated
  obtain ⟨meta_, L, hL, hLp⟩ :=
    pfx_newFromVk_proofLayout Features.solidity
      (Midfall.Generator.PlanNew.frFieldCtx R.E.delta) R.vk.cs rawMeta
      R.cfg.numInstances R.cfg.accumulator R.plan.vk plan hpl
  have h1 := (proofLen_eq_repackedLen meta_.protocol meta_.numEvals meta_.numPointSets L hL).1
  rw [← hp] at hLp
  rw [hLp]
  exact h1

/-! ## 2. The scalar/instance round trip for `frWord` -/

/-- `frOfWord?` inverts `frWord` on a canonical field element. PROVED. -/
theorem frOfWord?_frWord (hp : p < 2 ^ 256) (a : Fr p) :
    Midfall.LoweringV2.frOfWord? (p := p) (frWord a) = some a := by
  unfold Midfall.LoweringV2.frOfWord?
  rw [Midfall.Halo2.frWord_toNat hp a]
  rw [ite_eq_left (ZMod.val_lt a)]
  have hcast : ((ZMod.val a : ℕ) : Fr p) = a := by
    simpa using ZMod.natCast_val (R := Fr p) a
  exact congrArg some hcast

/-- `List.mapM frOfWord?` inverts `List.map frWord`. PROVED. -/
theorem mapM_frOfWord?_map_frWord (hp : p < 2 ^ 256) (l : List (Fr p)) :
    (l.map frWord).mapM (fun w => Midfall.LoweringV2.frOfWord? (p := p) w) = some l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.mapM_cons, frOfWord?_frWord hp a, ih]
      rfl

/-- `instOfWords?` inverts the canonical word image of an instance array. PROVED. -/
theorem instOfWords?_map_frWord (hp : p < 2 ^ 256) (l : List (Fr p)) :
    Midfall.LoweringV2.instOfWords? (p := p) (l.map frWord).toArray = some l.toArray := by
  unfold Midfall.LoweringV2.instOfWords?
  rw [List.toList_toArray, mapM_frOfWord?_map_frWord hp l]
  rfl

/-! ## 3. The forward direction of `EndToEndV3`, with the one schedule fact named -/

/-- **LEFT-TO-RIGHT, WITH THE READ-SCHEDULE AGREEMENT NAMED.** If the Rust-faithful
    decoder's messages have the render layout's slot shape, then a proof the Lean
    verifier accepts produces calldata on which every honest run returns. The proof is
    the V3 glue: `verifyNative_iff_msgs_codec`, `repack_spec_of_decodeRust`,
    `calldata_roundtrip`, the `frWord` round trip, and conjunct 2 of
    `LoweringEquivalenceV3`. -/
theorem end_to_end_forward_of_readSchedule (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : Midfall.LoweringV3.G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd)
    (hsched : ∀ ms : List (Msg (Fr p) G₁),
      decodeRust (Gₜ := Gₜ) R.E Features.solidity R.vk inst π = some ms →
        ms.map Msg.slot =
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots) :
    verifyNative (Gₜ := Gₜ) R.E Features.solidity R.params R.vk inst π = .ok () →
      ∃ cd, calldataOfV3 R π inst = .ok cd ∧
        ∀ st₀, EntryFrameV3 R W Lyt keccak256 cd st₀ →
          (∃ obs, RunBody R vkAddr 0 (callsOf product)
              (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
          ∀ obs, RunBody R vkAddr 0 (callsOf product)
              (ExternalGas.ofFun fun _ => 0) st₀ obs →
            obs.view = returnView st₀ := by
  intro hv
  -- The codec inversion: an accepted proof decodes to a message list Lean re-verifies.
  obtain ⟨ms, hdec, hvm⟩ :=
    (Midfall.Lowering.verifyNative_iff_msgs_codec (p := p) R.E Features.solidity R.params
      R.vk inst π hcodec.compressedRoundtrip).mp hv
  have hshape : ms.map Msg.slot =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots :=
    hsched ms hdec
  -- The encoder succeeds because the decoder's messages have the layout's shape.
  have hrep :
      Midfall.Lowering.repackProof (p := p)
        (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π =
        .ok (Midfall.Lowering.encodeContractProof (p := p) R.E.g1 ms) :=
    Midfall.Lowering.repack_spec_of_decodeRust (p := p) R.E Features.solidity R.vk inst π
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout)
      hcodec.compressedRoundtrip hsched ms hdec
  -- The calldata the encoder produces.
  let instL : List Word256 := inst.toList.map frWord
  let cd : Bytes := Midfall.Lowering.calldataOf (p := p) R.E.g1 ms instL
  have hcd : calldataOfV3 R π inst = .ok cd := by
    unfold calldataOfV3 Midfall.Lowering.repackThenEncode
    dsimp only [cd, instL]
    rw [hrep]
    simp only [Except.mapError]
    simp [hn]
    show Except.ok (Midfall.Lowering.encodeCalldataRaw
        (Midfall.Lowering.encodeContractProof R.E.g1 ms) (inst.toList.map frWord)) =
      Except.ok (Midfall.Lowering.calldataOf R.E.g1 ms (inst.toList.map frWord))
    rfl
  refine ⟨cd, hcd, ?_⟩
  intro st₀ hentry
  obtain ⟨hSound, hComplete⟩ := hside cd hcd
  -- The decoded calldata is exactly the one `calldataOf` writes, so Lean accepts it.
  have hplt : p < 2 ^ 256 := by
    rw [hR.env.modulus]
    norm_num [frModulusConstant]
  have hfacts := pfxFacts_of_validV3 (R := R) hR
  have hlen := proofLen_eq_repackedLen_of_validV3 R hR
  have hinstL : ∀ w ∈ instL, w.toNat < p := by
    intro w hw
    change w ∈ inst.toList.map frWord at hw
    obtain ⟨x, _hx, hxw⟩ := List.mem_map.mp hw
    rw [← hxw]
    exact Midfall.Halo2.frWord_toNat_lt hplt x
  have hnL : instL.length = R.cfg.numInstances := by
    simp [instL, hn]
  have hdecCd :
      decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instL.toArray) := by
    show decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1
      (Midfall.Lowering.calldataOf (p := p) R.E.g1 ms instL) = some (ms, instL.toArray)
    exact Midfall.Lowering.calldata_roundtrip (p := p) (G₁ := G₁) (le_of_lt hplt)
      R.plan.proofLayout hfacts.lCptr hlen hfacts.lEnd R.E.g1
      hcodec.toG1CodecLaws ms hshape R.cfg.numInstances instL hnL hinstL
  have hinstWords : Midfall.LoweringV2.instOfWords? (p := p) instL.toArray = some inst := by
    simpa [instL, Array.toArray_toList] using instOfWords?_map_frWord (p := p) hplt inst.toList
  have hacc : LeanAccepts R keccak256 cd :=
    ⟨ms, instL.toArray, inst, hdecCd, hinstWords, hvm⟩
  exact (hEq W Lyt keccak256 vkAddr cd st₀ hdep hentry hpc
    (Midfall.LoweringV3.G1CodecLawsV3.headline hcodec)).2.1 hacc hComplete

theorem list_take_add {α : Type} (l : List α) (n m : Nat) :
    l.take (n + m) = l.take n ++ (l.drop n).take m := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a as =>
          simp only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons, ih, List.cons_append]

theorem bytesTake_split (b : Bytes) (i n m : Nat) (h : i + n + m ≤ b.size) :
    bytesTake b i (n + m) =
      some ((bytesTake b i n).getD Bytes.empty ++
            (bytesTake b (i + n) m).getD Bytes.empty) := by
  have h1 : i + n ≤ b.size := by omega
  have h2 : i + (n + m) ≤ b.size := by omega
  unfold bytesTake
  rw [if_pos h2, if_pos h1, if_pos h]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [Option.getD_some, Array.toList_extract, List.extract_eq_take_drop]
  rw [Nat.add_sub_cancel_left]
  rw [list_take_add, List.drop_drop]
  rw [← ByteArray.append_eq, ByteArray.toList_data_append']
  simp only [Array.toList_extract, List.extract_eq_take_drop]
  rw [show i + n - i = n by omega, show i + n + m - (i + n) = m by omega]


theorem bytesTake_zero_of_le {b : Bytes} {i : Nat} (h : i ≤ b.size) :
    bytesTake b i 0 = some Bytes.empty := by
  unfold bytesTake
  rw [ite_eq_left (by omega : i + 0 ≤ b.size)]
  congr 1
  apply ByteArray.ext
  rw [Array.extract_eq_empty_of_le (by simp : min (i + 0) b.data.size ≤ i)]
  rfl

theorem bytesTake_whole (b : Bytes) : bytesTake b 0 b.size = some b := by
  unfold bytesTake
  rw [ite_eq_left (by omega : 0 + b.size ≤ b.size)]
  congr 1
  apply ByteArray.ext
  rw [show 0 + b.size = b.size by omega, Array.extract_eq_self_of_le (by simp : b.data.size ≤ b.size)]


theorem decodeGo_msg_slots {G : Type} (c : G1Codec G) (π : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat) (ms0 : List (Msg (Fr p) G))
      (ms : List (Msg (Fr p) G)) (cur' : Nat),
      slots.foldlM (Midfall.Lowering.decodeGo (p := p) c π) (ms0, cur) = some (ms, cur') →
      ∃ msTail, ms = ms0 ++ msTail ∧ msTail.map Msg.slot = slots := by
  intro slots
  induction slots with
  | nil =>
      intro cur ms0 ms cur' h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨[], by simp, rfl⟩
  | cons sl rest ih =>
      intro cur ms0 ms cur' h
      rw [List.foldlM_cons] at h
      change Option.bind (Midfall.Lowering.decodeGo (p := p) c π (ms0, cur) sl)
        (fun init => List.foldlM (Midfall.Lowering.decodeGo (p := p) c π) init rest) =
          some (ms, cur') at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨st, hstep, hrest⟩ := h
      obtain ⟨ms1, cur1⟩ := st
      rcases sl with _ | _
      · unfold Midfall.Lowering.decodeGo at hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨comp, hcomp, hstep⟩ := hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨Q, hQ, hstep⟩ := hstep
        obtain ⟨hms1, hcur1⟩ := Prod.mk.inj (Option.some.inj hstep)
        subst hms1
        subst hcur1
        obtain ⟨msTail, hms, hslots⟩ := ih (cur + Midfall.g1CompressedWidth)
          (ms0 ++ [Msg.g1 Q]) ms cur' hrest
        refine ⟨Msg.g1 Q :: msTail, ?_, ?_⟩
        · rw [hms]
          simp only [List.append_assoc, List.singleton_append]
        · simp only [List.map_cons, hslots]
          rfl
      · unfold Midfall.Lowering.decodeGo at hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨le, hle, hstep⟩ := hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨sc, hsc, hstep⟩ := hstep
        obtain ⟨hms1, hcur1⟩ := Prod.mk.inj (Option.some.inj hstep)
        subst hms1
        subst hcur1
        obtain ⟨msTail, hms, hslots⟩ := ih (cur + 32) (ms0 ++ [Msg.fr sc]) ms cur' hrest
        refine ⟨Msg.fr sc :: msTail, ?_, ?_⟩
        · rw [hms]
          simp only [List.append_assoc, List.singleton_append]
        · simp only [List.map_cons, hslots]
          rfl

theorem decodeWire_slots {G : Type} (plan : RepackedProofLayoutPlan) (c : G1Codec G)
    (π : Bytes) {ms : List (Msg (Fr p) G)}
    (h : Midfall.Lowering.decodeWire (p := p) plan c π = some ms) :
    ms.map Msg.slot = plan.slots := by
  unfold Midfall.Lowering.decodeWire at h
  by_cases hsize : π.size ≠ plan.compressedLen
  · rw [if_pos hsize] at h
    cases h
  · rw [if_neg hsize] at h
    have h' : (plan.slots.foldlM (Midfall.Lowering.decodeGo (p := p) c π) ([], 0)).map Prod.fst =
        some ms := h
    rcases hfold : plan.slots.foldlM (Midfall.Lowering.decodeGo (p := p) c π) ([], 0) with
      hnone | ⟨m2, c2⟩
    · rw [hfold] at h'
      cases h'
    · rw [hfold] at h'
      have hm : m2 = ms := by simpa using h'
      rw [← hm]
      obtain ⟨tail, hms, hslots⟩ := decodeGo_msg_slots c π plan.slots 0 [] m2 c2 hfold
      rw [hms]
      simpa using hslots


theorem decodeGo_wire (E : VerifierEnv p G₁ G₂ Gₜ)
    (hc : E.g1.compressedRoundtrip)
    (π : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat) (acc : Bytes) (ms0 : List (Msg (Fr p) G₁)),
      acc = ms0.foldl (init := Bytes.empty) (fun a m => a ++ Midfall.Halo2.msgWire E m) →
      cur + widthSum slots ≤ π.size →
      ∀ (ms : List (Msg (Fr p) G₁)) (cur' : Nat),
        slots.foldlM (Midfall.Lowering.decodeGo (p := p) E.g1 π) (ms0, cur) = some (ms, cur') →
        ∃ chunk, bytesTake π cur (widthSum slots) = some chunk ∧
          ms.foldl (init := Bytes.empty) (fun a m => a ++ Midfall.Halo2.msgWire E m) =
            acc ++ chunk := by
  intro slots
  induction slots with
  | nil =>
      intro cur acc ms0 hacc hsize ms cur' h
      change some (ms0, cur) = some (ms, cur') at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨Bytes.empty, bytesTake_zero_of_le (by simpa [widthSum] using hsize), ?_⟩
      rw [← hacc, show (Bytes.empty : Bytes) = ByteArray.empty from rfl, ByteArray.append_empty]
  | cons sl rest ih =>
      intro cur acc ms0 hacc hsize ms cur' h
      rw [List.foldlM_cons] at h
      change Option.bind (Midfall.Lowering.decodeGo (p := p) E.g1 π (ms0, cur) sl)
        (fun init => List.foldlM (Midfall.Lowering.decodeGo (p := p) E.g1 π) init rest) =
          some (ms, cur') at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨st, hstep, hrest⟩ := h
      obtain ⟨ms1, cur1⟩ := st
      rcases sl with _ | _
      · unfold Midfall.Lowering.decodeGo at hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨comp, hcomp, hstep⟩ := hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨Q, hQ, hstep⟩ := hstep
        obtain ⟨hms1, hcur1⟩ := Prod.mk.inj (Option.some.inj hstep)
        subst hms1
        subst hcur1
        have hwid : widthSum (WireSlot.g1 :: rest) =
            Midfall.g1CompressedWidth + widthSum rest := by
          rw [Midfall.Lowering.widthSum_cons]
          rfl
        have hsize' : cur + Midfall.g1CompressedWidth + widthSum rest ≤ π.size := by
          rw [hwid] at hsize
          omega
        have hacc' : acc ++ Midfall.Halo2.msgWire E (Msg.g1 Q) =
            (ms0 ++ [Msg.g1 Q]).foldl (init := Bytes.empty)
              (fun a m => a ++ Midfall.Halo2.msgWire E m) := by
          rw [List.foldl_append]
          rw [hacc]
          rfl
        obtain ⟨chunk', htake', hfold'⟩ :=
          ih (cur + Midfall.g1CompressedWidth) (acc ++ Midfall.Halo2.msgWire E (Msg.g1 Q))
            (ms0 ++ [Msg.g1 Q]) hacc' hsize' ms cur' hrest
        have hcomp' : Midfall.Halo2.msgWire E (Msg.g1 Q) = comp := hc comp Q hQ
        have hsplit := bytesTake_split π cur Midfall.g1CompressedWidth (widthSum rest) hsize'
        rw [hcomp, htake'] at hsplit
        simp only [Option.getD_some] at hsplit
        refine ⟨comp ++ chunk', ?_, ?_⟩
        · rw [hwid]
          exact hsplit
        · rw [hfold', hcomp', ByteArray.append_assoc]
      · unfold Midfall.Lowering.decodeGo at hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨le, hle, hstep⟩ := hstep
        rw [Option.bind_eq_some_iff] at hstep
        obtain ⟨sc, hsc, hstep⟩ := hstep
        obtain ⟨hms1, hcur1⟩ := Prod.mk.inj (Option.some.inj hstep)
        subst hms1
        subst hcur1
        have hwid : widthSum (WireSlot.fr :: rest) = 32 + widthSum rest := by
          rw [Midfall.Lowering.widthSum_cons]
          rfl
        have hsize' : cur + 32 + widthSum rest ≤ π.size := by
          rw [hwid] at hsize
          omega
        have hacc' : acc ++ Midfall.Halo2.msgWire E (Msg.fr sc) =
            (ms0 ++ [Msg.fr sc]).foldl (init := Bytes.empty)
              (fun a m => a ++ Midfall.Halo2.msgWire E m) := by
          rw [List.foldl_append]
          rw [hacc]
          rfl
        obtain ⟨chunk', htake', hfold'⟩ :=
          ih (cur + 32) (acc ++ Midfall.Halo2.msgWire E (Msg.fr sc))
            (ms0 ++ [Msg.fr sc]) hacc' hsize' ms cur' hrest
        have hsc' : Midfall.Halo2.msgWire E (Msg.fr sc) = le :=
          Midfall.Assumptions.frOfRepr_frToRepr_bytes (p := p) hsc
        have hsplit := bytesTake_split π cur 32 (widthSum rest) hsize'
        rw [hle, htake'] at hsplit
        simp only [Option.getD_some] at hsplit
        refine ⟨le ++ chunk', ?_, ?_⟩
        · rw [hwid]
          exact hsplit
        · rw [hfold', hsc', ByteArray.append_assoc]

theorem decodeWire_wire (E : VerifierEnv p G₁ G₂ Gₜ)
    (hc : E.g1.compressedRoundtrip) (plan : RepackedProofLayoutPlan)
    (π : Bytes) {ms : List (Msg (Fr p) G₁)}
    (h : Midfall.Lowering.decodeWire (p := p) plan E.g1 π = some ms) :
    π = ms.foldl (init := Bytes.empty) (fun a m => a ++ Midfall.Halo2.msgWire E m) := by
  unfold Midfall.Lowering.decodeWire at h
  by_cases hsize : π.size ≠ plan.compressedLen
  · rw [if_pos hsize] at h
    cases h
  · rw [if_neg hsize] at h
    have h' : (plan.slots.foldlM (Midfall.Lowering.decodeGo (p := p) E.g1 π) ([], 0)).map Prod.fst =
        some ms := h
    have hlen : π.size = plan.compressedLen := by omega
    rcases hfold : plan.slots.foldlM (Midfall.Lowering.decodeGo (p := p) E.g1 π) ([], 0) with
      hnone | ⟨m2, c2⟩
    · rw [hfold] at h'
      cases h'
    · rw [hfold] at h'
      have hm : m2 = ms := by simpa using h'
      have hsizeW : 0 + widthSum plan.slots ≤ π.size := by
        rw [hlen, Midfall.Lowering.compressedLen_eq_widthSum]
        omega
      obtain ⟨chunk, htake, hwire⟩ :=
        decodeGo_wire (p := p) E hc π plan.slots 0 Bytes.empty [] rfl hsizeW m2 c2 hfold
      have hchunk : chunk = π := by
        have hwhole := bytesTake_whole π
        have htake' : bytesTake π 0 π.size = some chunk := by
          rw [hlen, Midfall.Lowering.compressedLen_eq_widthSum]
          exact htake
        exact Option.some.inj (htake'.symm.trans hwhole)
      rw [hm, hchunk] at hwire
      simpa [show (Bytes.empty : Bytes) = ByteArray.empty from rfl,
        ByteArray.empty_append] using hwire.symm



theorem except_mapError_ok {ε ε' α : Type} {f : ε → ε'} {m : Except ε α} {a : α}
    (h : m.mapError f = .ok a) : m = .ok a := by
  cases m with
  | ok b =>
      cases h
      rfl
  | error e => cases h


theorem end_to_end_backward (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd) :
    (∃ cd, calldataOfV3 R π inst = .ok cd ∧
      ∀ st₀, EntryFrameV3 R W Lyt keccak256 cd st₀ →
        (∃ obs, RunBody R vkAddr 0 (callsOf product)
            (ExternalGas.ofFun fun _ => 0) st₀ obs) ∧
        ∀ obs, RunBody R vkAddr 0 (callsOf product)
            (ExternalGas.ofFun fun _ => 0) st₀ obs →
          obs.view = returnView st₀) →
    verifyNative (Gₜ := Gₜ) R.E Features.solidity R.params R.vk inst π = .ok () := by
  rintro ⟨cd, hcdok, hrun⟩
  unfold calldataOfV3 Midfall.Lowering.repackThenEncode at hcdok
  obtain ⟨proof, hmap, hif⟩ := Midfall.Lowering.except_bind_ok _ _ hcdok
  have hrep : Midfall.Lowering.repackProof (p := p)
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π = .ok proof :=
    except_mapError_ok hmap
  have hcdEq : cd = Midfall.Lowering.encodeCalldataRaw proof (inst.toList.map frWord) := by
    by_cases hne : inst.size ≠ R.cfg.numInstances
    · rw [ite_eq_left hne] at hif
      cases hif
    · rw [ite_eq_right hne] at hif
      exact (Except.ok.inj hif).symm
  obtain ⟨ms, hdecWire, hproofEq⟩ :=
    (Midfall.Lowering.repack_spec_wire (p := p)
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) R.E.g1 π proof).mp hrep
  have hshape : ms.map Msg.slot =
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots :=
    decodeWire_slots (p := p) (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout)
      R.E.g1 π hdecWire
  have hwire : π = ms.foldl (init := Bytes.empty)
      (fun a m => a ++ Midfall.Halo2.msgWire R.E m) :=
    decodeWire_wire (p := p) R.E hcodec.compressedRoundtrip
      (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout) π hdecWire
  let instL : List Word256 := inst.toList.map frWord
  have hcdEq' : cd = Midfall.Lowering.calldataOf (p := p) R.E.g1 ms instL := by
    rw [hcdEq, hproofEq]
    rfl
  have hplt : p < 2 ^ 256 := by
    rw [hR.env.modulus]
    norm_num [frModulusConstant]
  have hfacts := pfxFacts_of_validV3 (R := R) hR
  have hlen := proofLen_eq_repackedLen_of_validV3 R hR
  have hinstL : ∀ w ∈ instL, w.toNat < p := by
    intro w hw
    change w ∈ inst.toList.map frWord at hw
    obtain ⟨x, _hx, hxw⟩ := List.mem_map.mp hw
    rw [← hxw]
    exact Midfall.Halo2.frWord_toNat_lt hplt x
  have hnL : instL.length = R.cfg.numInstances := by
    simp [instL, hn]
  have hdecCd :
      decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd =
        some (ms, instL.toArray) := by
    rw [hcdEq']
    exact Midfall.Lowering.calldata_roundtrip (p := p) (G₁ := G₁) (le_of_lt hplt)
      R.plan.proofLayout hfacts.lCptr hlen hfacts.lEnd R.E.g1
      hcodec.toG1CodecLaws ms hshape R.cfg.numInstances instL hnL hinstL
  have hsel : bytesTake cd 0 4 = some Midfall.Generator.fnSigVerifyProof := by
    rw [hcdEq]
    unfold Midfall.Lowering.encodeCalldataRaw Midfall.Generator.encodeCalldata
    simp only [Midfall.Generator.bytesFromNats, Midfall.Generator.bytesToNats,
      Midfall.Generator.fnSigVerifyProof, bytesTake]
    rfl
  have hcdSizeEq := Midfall.LoweringV3.cdSize_of_decodes (p := p) R.plan.proofLayout
    R.cfg.numInstances R.E.g1 cd ms instL.toArray hdecCd
  have hcdSize : cd.size < 2 ^ 256 := by
    rw [hcdSizeEq]
    exact cdBound_of_valid hR
  obtain ⟨st₀, hentry⟩ :=
    entryFrame_inhabitedV3 R W Lyt keccak256 cd hsel hcv
      (transcriptMptr_of_valid hR) hcdSize
  obtain ⟨⟨obs, hobs⟩, hviewAll⟩ := hrun st₀ hentry
  have hview := hviewAll obs hobs
  have hret : obs.isReturn := (isReturn_of_view_eq hview).mpr ⟨abiTrue, rfl⟩
  have hperm : RunBody R vkAddr 0 (permissive (callsOf product))
      (ExternalGas.ofFun fun _ => 0) st₀ obs :=
    runBody_mono R vkAddr 0 (callsOf product) (permissive (callsOf product))
      (ExternalGas.ofFun fun _ => 0) st₀ obs (callsOf_le_permissive product) hobs
  obtain ⟨hSound, _hComplete⟩ := hside cd hcdok
  have hsnd := (hEq W Lyt keccak256 vkAddr cd st₀ hdep hentry hpc
    (Midfall.LoweringV3.G1CodecLawsV3.headline hcodec)).1
      (ExternalGas.ofFun fun _ => 0) obs hperm hret hSound
  obtain ⟨ms', instW', inst', hdec', hinst', hvm'⟩ := hsnd.2
  have hpair : (ms', instW') = (ms, instL.toArray) :=
    Option.some.inj (hdec'.symm.trans hdecCd)
  obtain ⟨hms', hinstW'⟩ := Prod.mk.inj hpair
  subst hms'
  subst hinstW'
  have hinstEq : inst' = inst := by
    have hw : Midfall.LoweringV2.instOfWords? (p := p) instL.toArray = some inst := by
      simpa [instL, Array.toArray_toList] using instOfWords?_map_frWord (p := p) hplt inst.toList
    exact Option.some.inj (hinst'.symm.trans hw)
  subst hinstEq
  rw [Midfall.Halo2.verifyMsgs_eq_verifyShape] at hvm'
  rw [Midfall.Halo2.verifyNative_eq_verifyShape]
  rw [hwire, ← Midfall.Halo2.Transcript.initWithHash_keccak]
  exact hvm'


theorem end_to_end_of_readSchedule (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (hR : ValidV3 R) (hEq : LoweringEquivalenceV3 R product)
    (W : ExecEnv) (Lyt : EVM.Layout) (vkAddr : U256)
    (hdep : DeploymentV2 R W keccak256 vkAddr) (hcv : W.callvalue = 0)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) (hcodec : G1CodecLawsV3 R.E.g1)
    (inst : Array (Fr p)) (π : Bytes) (hn : inst.size = R.cfg.numInstances)
    (hside : ∀ cd, calldataOfV3 R π inst = .ok cd →
      SoundSide R keccak256 cd ∧ CompleteSide R keccak256 cd)
    (hsched : ∀ ms : List (Msg (Fr p) G₁),
      decodeRust (Gₜ := Gₜ) R.E Features.solidity R.vk inst π = some ms →
        ms.map Msg.slot =
          (RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout).slots) :
    EndToEndV3 R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec inst π hn hside := by
  unfold EndToEndV3
  constructor
  · intro hv
    exact end_to_end_forward_of_readSchedule R product hR hEq W Lyt vkAddr hdep hcv hpc
      hcodec inst π hn hside hsched hv
  · intro hrhs
    exact end_to_end_backward R product hR hEq W Lyt vkAddr hdep hcv hpc hcodec
      inst π hn hside hrhs

theorem logDispatch_slot (E : VerifierEnv p G₁ G₂ Gₜ) (rec : Nat × Bytes)
    (m : Msg (Fr p) G₁)
    (hw : rec.1 = 32 ∨ rec.1 = g1CompressedWidth)
    (h : logDispatch E rec = some m) :
    Msg.slot m =
      if rec.1 = g1CompressedWidth then WireSlot.g1 else WireSlot.fr := by
  have htwo : logDispatch E rec =
      (if rec.1 == (hashableG1 E.g1).width then (E.g1.ofCompressed? rec.2).map Msg.g1
        else (frOfRepr? (p := p) rec.2).map Msg.fr) := by
    unfold logDispatch
    rw [hashableG1_width, hashableFr_width]
    exact widthDispatch_exhaustive (fun b => (E.g1.ofCompressed? b).map Msg.g1)
      (fun b => (frOfRepr? (p := p) b).map Msg.fr) rec hw
  rw [htwo, hashableG1_width] at h
  by_cases hg : (rec.1 == g1CompressedWidth) = true
  · rw [if_pos hg] at h
    cases hq : E.g1.ofCompressed? rec.2 with
    | none => rw [hq] at h; cases h
    | some Q =>
        rw [hq, Option.map_some] at h
        have hm : Msg.g1 Q = m := Option.some.inj h
        subst hm
        have hrec : rec.1 = g1CompressedWidth := of_decide_eq_true hg
        simp [Msg.slot, hrec]
  · rw [if_neg hg] at h
    cases hq : frOfRepr? (p := p) rec.2 with
    | none => rw [hq] at h; cases h
    | some s =>
        rw [hq, Option.map_some] at h
        have hm : Msg.fr s = m := Option.some.inj h
        subst hm
        have hne : ¬ rec.1 = g1CompressedWidth := by
          intro hrec
          exact hg (by rw [hrec]; exact beq_self_eq_true _)
        have hrec32 : rec.1 = 32 := by
          rcases hw with h32 | h48
          · exact h32
          · exact absurd h48 hne
        simp only [Msg.slot, hne, if_neg]
        rfl

theorem list_mapM_slot (E : VerifierEnv p G₁ G₂ Gₜ) :
    ∀ (l : List (Nat × Bytes)) (ms : List (Msg (Fr p) G₁)),
      (∀ rec ∈ l, rec.1 = 32 ∨ rec.1 = g1CompressedWidth) →
      l.mapM (logDispatch E) = some ms →
      ms.map Msg.slot =
        l.map (fun r =>
          if r.1 = g1CompressedWidth then WireSlot.g1 else WireSlot.fr) := by
  intro l
  induction l with
  | nil =>
      intro ms _ h
      cases h
      rfl
  | cons a as ih =>
      intro ms hw h
      rw [List.mapM_cons] at h
      change Option.bind (logDispatch E a)
        (fun b => Option.bind (List.mapM (logDispatch E) as)
          (fun bs => some (b :: bs))) = some ms at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, hrest⟩ := h
      change Option.bind (List.mapM (logDispatch E) as)
        (fun bs => some (m :: bs)) = some ms at hrest
      rw [Option.bind_eq_some_iff] at hrest
      obtain ⟨msTail, hms, hsome⟩ := hrest
      have hmsEq : m :: msTail = ms := Option.some.inj hsome
      have hw' : ∀ rec ∈ as, rec.1 = 32 ∨ rec.1 = g1CompressedWidth :=
        fun rec hrec => hw rec (List.mem_cons_of_mem a hrec)
      have hslots := ih msTail hw' hms
      rw [← hmsEq]
      simp only [List.map_cons]
      rw [logDispatch_slot E a m (hw a List.mem_cons_self) hm, hslots]

theorem decodeRust_slots_eq_logWidths (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes)
    {ms : List (Msg (Fr p) G₁)}
    (hdec : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    ∃ t : Transcript,
      ms.map Msg.slot =
        t.log.toList.map (fun r =>
          if r.1 = g1CompressedWidth then WireSlot.g1 else WireSlot.fr) := by
  obtain ⟨d, t, hrun, hpos, hmap⟩ := decodeRust_some E F vk inst π ms hdec
  have hw : ∀ rec ∈ t.log.toList, rec.1 = 32 ∨ rec.1 = g1CompressedWidth := by
    have hpres : PresWidths (prepare (Gₜ := Gₜ) E F vk [[1]] [[inst.toList]]) :=
      presWidths_prepare (p := p) E F vk [[1]] [[inst.toList]]
    exact hpres (Transcript.initFromBytes π) t d
      (Transcript.LogWidths.initFromBytes π) hrun
  exact ⟨t, list_mapM_slot E t.log.toList ms hw hmap⟩


/-- **THE NAMED D1 BLOCKER.** `ValidV3` pins the plan to the generator
    (`generated`), and `SupportedV2.layout` pins only the MEMORY map. Neither pins
    the verifier's read order: `decodeRust` is a run of `Verifier.prepare`, while
    `plan.slots` is the layout built from `ConstraintSystemMeta.new R.vk.cs`. A
    proof needs a verifier-vs-protocol refinement (`prepare`'s log widths equal the
    protocol's proof-read plan), which is not in the tree. This string is the
    handoff; it is NOT a hypothesis on any theorem. -/
def gap_readScheduleAgrees : String :=
  "D1 blocker: readScheduleAgrees_of_validV3. ValidV3.generated pins R.plan to " ++
    "generateAll, so plan.proofLayout is from ProtocolPlan.fromConstraintSystem on " ++
    "R.vk.cs; but no theorem relates the WIDTH SEQUENCE of Verifier.prepare (hence " ++
    "decodeRust) to that protocol plan. SupportedV2.layout is the memory-map check " ++
    "only. PROVED REDUCTION: decodeRust_slots_eq_logWidths below shows " ++
    "ms.map Msg.slot IS t.log.toList.map width, so only the static width list " ++
    "remains. Smallest true bridge: prepare_logSlots — for every successful " ++
    "(prepare ...).run, the log widths are replicate prefixG1Count g1 ++ " ++
    "replicate numEvals fr ++ [g1] ++ replicate numPointSets fr ++ [g1]. " ++
    "Sub-facts still to prove: (a) parseTrace appends replicate " ++
    "nonQuotientCommitmentCount g1; (b) readAlgebra appends replicate " ++
    "nbQuotient g1 ++ replicate evalReadCount fr; (c) multiPrepare appends " ++
    "[g1] ++ replicate qEvalSetCount fr ++ [g1]; (d) qEvalSetCount = " ++
    "R.plan.meta_.numPointSets and the counts match the protocol fields " ++
    "(prefixG1Count + nbQuotient, numEvals, numPointSets). (d)'s qEval count " ++
    "is the generator's intermediateSets.pointSets.length vs the verifier's " ++
    "MultiOpen.phaseA qEvalSets.size. With prepare_logSlots, " ++
    "decodeRust_slots_eq_logWidths gives ms.map Msg.slot = plan.slots and " ++
    "end_to_end_of_readSchedule is end_to_end."



#print axioms proofLen_eq_repackedLen_of_validV3
#print axioms frOfWord?_frWord
#print axioms mapM_frOfWord?_map_frWord
#print axioms instOfWords?_map_frWord

#check @end_to_end_forward_of_readSchedule
#check @end_to_end_backward
#check @end_to_end_of_readSchedule

#cone_sorries Midfall.LoweringV3.end_to_end_of_readSchedule

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_of_readSchedule
  [propext, Classical.choice, Quot.sound, sorryAx] native []

#cone_sorries Midfall.LoweringV3.end_to_end_forward_of_readSchedule

open Midfall.Tools.Done in
#assert_axioms Midfall.LoweringV3.end_to_end_forward_of_readSchedule
  [propext, Classical.choice, Quot.sound, sorryAx] native []

end Midfall.LoweringV3

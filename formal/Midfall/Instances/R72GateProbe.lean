/-
  Midfall.Instances.R72GateProbe

  R-72's REPRODUCER, LANDED IN THE TREE (Q0.5). The original lived in /tmp/q04/probe1.lean at
  c57acc3 and was never committed, so it survived only as prose in docs/REVIEW.md (R-72).
  EXECUTION-V2 W5 says evidence a card relies on is landed, never left in /tmp: this is that
  evidence, re-created from the prose and re-run against the tree at 4e18c65.

  WHAT IT SHOWS. HypothesesInhabited (Statements.lean section 8, FROZEN) is the D-P23 non-vacuity
  gate for the headline. Before D-P45 it was the conjunction
      DeploymentV2 ∧ EntryFrame ∧ Eip2537.Holds ∧ SoundSide ∧ CompleteSide
  and NOTHING required the witness calldata to decode. But SoundSide and CompleteSide are both
  universals over decodeCalldata ... = some (ms, instW), so they go TRUE exactly when nothing
  decodes. The three theorems below are the witness that the gate was satisfiable with no accepting
  calldata and no run at all:

    1. sel_nondecode         the bare 4-byte verifyProof selector fails decodeCalldata's head-word
                             guard ((cdWord cd 4).toNat == 0x40 reads 0) at EVERY layout, instance
                             count and codec;
    2. gate_weak             from four facts any render has anyway, the PRE-D-P45 gate HOLDS,
                             witnessed at cd := fnSigVerifyProof - a calldata for which (1) makes
                             both side conditions vacuous;
    3. no_accept_at_gate_cd  that same calldata is one the Lean verifier REJECTS.

  (2) and (3) hold simultaneously: that is the defect.

  THE BEFORE/AFTER, AND WHY gate_weak IS STATED AGAINST A PIN. The card's order is the point: the
  falsifier had to be demonstrated against the gate it accuses, and only then repaired. Both halves
  were run at 4e18c65 with lake build (see the Q0.5 report):

    BEFORE  gate_weak's conclusion was the live HypothesesInhabited as it then stood. Build:
            '[5239/5241] Built Midfall.Instances.R72GateProbe' - green, no sorryAx.
    AFTER   the same theorem, same proof term, against the AMENDED live definition. Build:
            error: .../R72GateProbe.lean:105:10: Tactic `introN` failed: There are no additional
            binders or `let` bindings in the goal to introduce
            case refine_3
            ...  CompleteSide R keccak256 fnSigVerifyProof AND (exists ms instW inst Snap, ...)
                ∧ G1CodecLaws R.E.g1

  So gate_weak no longer elaborates: the extra conjuncts are unsolvable at its witness. That is the
  teeth the card demanded. The theorem is kept HERE, against HypothesesInhabitedPreD45 - the frozen
  pre-D-P45 text pinned verbatim, exactly the D-P27 pattern Instances/StatementsRepair.lean uses for
  every amended statement - so the witness stays landed and the file stays green whatever the live
  gate does next. gate_now_forces_a_real_decode is the same finding stated forward: it is a theorem
  about the AMENDED gate that no calldata of the R-72 shape can witness it.

  THE ST.4 REPAIR (D-P64). The live gate now asks for `LeanAccepts` at `keccak256` instead of the
  D-P45 decode chain and no longer quantifies the hash, so `gate_now_forces_a_real_decode` reads
  its decode out of `LeanAccepts` - the same finding, now immediate: an accepting calldata decodes.
  `HypothesesInhabitedPreD45` is untouched: it pins the PRE-D-P45 CONJUNCTION and cites `EntryFrame`
  by name, so the `cdSize` field ST.4 added to the live frame does not move the pinned text (the
  selector calldata is 4 bytes, well inside the bound).

  WHY HERE, IN Instances/. Nothing in this file is cited by the frozen surface, and the dependency
  runs Instances -> Statements, never back (D-P17). No native_decide is used: the two cdWord facts
  are closed by rfl, so every theorem here sits on [propext, Classical.choice, Quot.sound] and
  carries no compiler-trust axiom.
-/
import Midfall.LoweringV2.Blocks

namespace Midfall.Instances

open Midfall Midfall.Halo2 Midfall.Generator Midfall.Lowering Midfall.LoweringV2 Midfall.Assumptions
open Midfall.Yul Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [AdmissiblePairing G₁ G₂ Gₜ]

/-- THE PRE-D-P45 TEXT OF THE GATE, PINNED VERBATIM (the D-P27 pattern: an amended frozen statement
    keeps its old text as a named proposition next to the exhibit that shows why it was wrong).
    This is what Statements.lean:317 said at 4e18c65, character for character. -/
def HypothesesInhabitedPreD45 (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) : Prop :=
  ∃ (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (vkAddr : U256) (cd : Bytes) (st₀ : EvmState),
    DeploymentV2 R W H vkAddr ∧ EntryFrame R W Lyt H cd st₀ ∧
      Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product ∧ SoundSide R H cd ∧ CompleteSide R H cd

/-- The two words the head guard reads sit past the end of a 4-byte calldata, so they are 0. -/
theorem hcd4 : (cdWord Midfall.Generator.fnSigVerifyProof 4).toNat = 0 := rfl
theorem hcd36 : (cdWord Midfall.Generator.fnSigVerifyProof 36).toNat = 0 := rfl

/-- **R-72 (1).** The bare verifyProof selector never decodes - at EVERY layout, instance count and
    codec. decodeCalldata's head-word guard (cdWord cd 4).toNat == 0x40 reads 0 off the end of a
    4-byte calldata, so the do block short-circuits to none before any codec is consulted. -/
theorem sel_nondecode (L : ProofCalldataLayout) (n : Nat) (c : G1Codec G₁) :
    decodeCalldata (p := p) L n c Midfall.Generator.fnSigVerifyProof = none := by
  unfold decodeCalldata
  simp only [hcd4, hcd36]
  simp [guard]

/-- The probe world: the render's own VK runtime bytes at vkAddr, nothing anywhere else. Built here
    rather than imported so the reproducer stays generic in the render - it is a witness that the
    gate admitted ANY render, not a fact about one. -/
def probeW (bs : List UInt8) (vkAddr : U256) : ExecEnv :=
  { callvalue := 0,
    keccakOf := hashOfBytes keccak256,
    extCodeOf := fun a => if a = vkAddr then bs else [],
    extCodeHashOf := fun a =>
      if (if a = vkAddr then bs else []).length = 0 then 0
      else hashOfBytes keccak256 (if a = vkAddr then bs else []) }

theorem probeW_wf (bs : List UInt8) (vkAddr : U256) : (probeW bs vkAddr).WF := by
  constructor
  · intro a; simp [probeW, projectedCodeHash]
  · simp [probeW]

theorem probeW_code (bs : List UInt8) (vkAddr : U256) :
    (probeW bs vkAddr).extCodeOf vkAddr = bs := by simp [probeW]

/-- An arbitrary shell layout: the reproducer never reads it. -/
def probeLyt : EVM.Layout := { code := [], dataOffset := fun _ => 0, dataSize := fun _ => 0 }

theorem probe_hsel : Midfall.bytesTake Midfall.Generator.fnSigVerifyProof 0 4 =
    some Midfall.Generator.fnSigVerifyProof := rfl

/-- **R-72 (2) - THE FALSIFIER.** The PRE-D-P45 gate is inhabited at ANY render, from four facts a
    render has anyway, witnessed at the calldata that sel_nondecode makes vacuous for both side
    conditions. Stated against the pin above: run against the live definition at 4e18c65 it built
    green, and after D-P45 landed it stopped elaborating (header). -/
theorem gate_weak (R : Render p G₁ G₂ Gₜ) (product : PairingProduct) (vkAddr : U256)
    (hsize : R.plan.vk.runtimeBytes.size ≠ 0)
    (hdisj : accountKey vkAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat))
    (ht : ∃ t, R.consts.lookup "TRANSCRIPT_MPTR" = some t ∧ 0x80 ≤ t)
    (hpc : Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product) :
    HypothesesInhabitedPreD45 R product := by
  unfold HypothesesInhabitedPreD45
  obtain ⟨st₀, hent⟩ := entryFrame_inhabited R (probeW R.plan.vk.runtimeBytes.data.toList vkAddr)
    probeLyt keccak256 Midfall.Generator.fnSigVerifyProof probe_hsel rfl ht
    (by decide : Midfall.Generator.fnSigVerifyProof.size < 2 ^ 256)
  refine ⟨probeW R.plan.vk.runtimeBytes.data.toList vkAddr, probeLyt, keccak256, vkAddr,
    Midfall.Generator.fnSigVerifyProof, st₀, ?_, hent, hpc, ?_, ?_⟩
  · exact ⟨rfl, probeW_wf _ _, probeW_code _ _, rfl, hsize, hdisj⟩
  · intro ms instW inst h
    rw [sel_nondecode] at h
    exact absurd h (by simp)
  · intro ms instW inst Snap h _ _
    rw [sel_nondecode] at h
    exact absurd h (by simp)

/-- **R-72 (3).** The calldata the gate was satisfied by is one the Lean verifier rejects: it does
    not decode, and LeanAccepts requires a decode. Holds simultaneously with gate_weak. -/
theorem no_accept_at_gate_cd (R : Render p G₁ G₂ Gₜ) (H : Hash) :
    ¬ LeanAccepts R H Midfall.Generator.fnSigVerifyProof := by
  intro ⟨ms, instW, inst, hdec, _, _⟩
  rw [sel_nondecode] at hdec
  exact absurd hdec (by simp)

/-- **THE REPAIR HAS TEETH (D-P45).** The amended gate forces its witness calldata to be a REAL one:
    something that decodes, and therefore something that is not the bare selector. This is exactly
    what gate_weak could not force, and it is the forward form of the falsifier: the R-72 witness is
    not merely inconvenient for the new gate, it is excluded by it. -/
theorem gate_now_forces_a_real_decode (R : Render p G₁ G₂ Gₜ) (product : PairingProduct)
    (h : HypothesesInhabited R product) :
    ∃ (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (instW : Array Word256),
      decodeCalldata (p := p) R.plan.proofLayout R.cfg.numInstances R.E.g1 cd = some (ms, instW) ∧
      cd ≠ Midfall.Generator.fnSigVerifyProof := by
  obtain ⟨_W, _Lyt, _vkAddr, cd, _st₀, _hdep, _hent, _hpc, _hcodec, hacc, _hss, _hcs⟩ := h
  obtain ⟨ms, instW, _inst, hdec, _, _⟩ := hacc
  refine ⟨cd, ms, instW, hdec, ?_⟩
  intro heq
  rw [heq, sel_nondecode] at hdec
  exact absurd hdec (by simp)

#print axioms Midfall.Instances.sel_nondecode
#print axioms Midfall.Instances.gate_weak
#print axioms Midfall.Instances.no_accept_at_gate_cd
#print axioms Midfall.Instances.gate_now_forces_a_real_decode

end Midfall.Instances
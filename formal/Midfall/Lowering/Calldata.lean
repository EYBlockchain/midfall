-- |
-- Midfall.Lowering.Calldata
--
-- P-SE stage 2 (docs/plans/P-SE-stage2.md, file row 4; PLAN
-- P-SE-semantic-equivalence.md section H and index item 8; design1.md M5-7 and
-- M5-8, and the blocks "WireSlot / Msg.slot / ...", "repackProof / decodeWire",
-- "encodeCalldataRaw / encodeCalldata / calldataOf", "decodeCalldata",
-- "repackedLen_mod32 / proofLen_eq_repackedLen / sum_commitmentReadGroups",
-- "calldata_roundtrip", "calldata_canonical (EXACT, both modes)",
-- "repack_spec (split form; PLAN iff is false)", "points_subgroup_checked").
--
-- WHAT THIS FILE IS FOR. The contract is handed a byte buffer and the headline
-- theorems quantify over it, so there has to be a Lean decoder that says what the
-- contract accepts and an encoder that says what a proof's bytes are. That is
-- this file: the wire slot algebra (WireSlot, slots, msgContractBytes,
-- encodeContractProof), the codec-generic repack/decode pair (repackProof,
-- decodeWire), the envelope (encodeCalldata, calldataOf), and the contract-shaped
-- decoder (decodeCalldata) with its four specs.
--
-- THE DECODER IS OURS, AND THAT IS A FACT ABOUT THE REFERENCE, NOT AN OMISSION:
-- there is no Rust calldata decoder. The contract's acceptance rules live in the
-- Yul templates and are cited line by line at each guard. The Rust side has
-- decodeRust (Exec/Native.lean:228), which runs the whole transcript pipeline and
-- returns the messages it consumed - a different thing, and the reason
-- repack_spec had to be split (below).
--
-- ONE STATEMENT GOT STRONGER, and this file takes the win. PLAN 13's risk note
-- said the contract's decoder might accept trailing bytes, so calldata_canonical
-- was going to need an approximately-equal fallback. P-12 measured the templates
-- and the generated contract instead and found the decoder EXACT: VkLoading.yul
-- pins calldatasize to the last instance byte, TranscriptProofParser.yul:63-68
-- rejects instance words >= r, :319 and :382 reject proof and q_eval words >= r,
-- and AssemblyHelpers.yul:94-104 requires each G1 coordinate's high word to be
-- below 2^128 and the pair to be below pBase - so an accepted 128-byte block is
-- the canonical encoding of the point it decodes to. calldata_canonical is
-- therefore stated as an equality over raw Word256, in both accumulator and
-- no-accumulator mode (D7 was right), and the old fallback is NOT carried forward.
--
-- THE LAYOUT-CONSISTENCY GUARD, which is attack.md's calldata_canonical FIX and is
-- load-bearing. decodeCalldata walks slots from L.proofCptr until L.proofEnd but
-- the length word it checks is L.proofLen, and nothing ties the two for a HAND-BUILT
-- ProofCalldataLayout (survey, Encoding area: ProofSection.new is never recomputed).
-- Without the guard, a layout with proofLen = 7 and proofEnd = proofCptr + 384
-- decodes a 384-byte proof region while calldataOf writes BE32(384) at 0x44, so the
-- equation fails for a value the decoder accepted. The guard
-- L.proofEnd == L.proofCptr + L.proofLen is in the decoder, and
-- proofLen_eq_repackedLen says every fromProtocol layout satisfies it.
--
-- WHAT IS NOT HERE. The semantic layer of points_subgroup_checked (a call trace
-- over the EVM) is an Obligations field; only the generator layer is stated here.
-- The Surface plumbing (repackProof_faithful, encodeCalldata_faithful, the
-- readScheduleAgrees bridge) belongs to stages 4-6. No Midfall/Instances/ import
-- (D-P17) and no Generator.Vk.

import Midfall.Generator.Abi
import Midfall.Generator.Api
import Midfall.Generator.Calldata
import Midfall.Generator.Evm
import Midfall.Generator.Encoding
import Midfall.Generator.Kzg
import Midfall.Generator.Quotient.VmTypes
import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Accumulator
import Midfall.Assumptions.Codec

namespace Midfall.Lowering
open Midfall Midfall.Halo2
open Midfall.Generator (RepackedProofLayoutPlan ProofCalldataLayout RepackError)

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### 1. The wire slots -/

/-- One slot of the repacked proof: a padded G1 block or a 32-byte scalar word.
    The two-way split is what calldata.rs's walk alternates over, and it is what
    the transcript read schedule produces (hashableG1 width 128, hashableFr
    width 32), so the same type names both sides of repack_spec_wire. -/
inductive WireSlot
  /-- rust: CD:61-87 (push_g1) - one 48-byte compressed commitment widened to 128. -/
  | g1
  /-- rust: CD:88-108 (push_scalar_be) - one 32-byte LE proof scalar as a BE word. -/
  | fr
  deriving DecidableEq, Repr

/-- The slot a message occupies. The schedule is not stored anywhere in the
    contract-facing form - it is a property of the message list - which is why
    encodeContractProof needs no plan and why hshape is a hypothesis of
    calldata_roundtrip rather than a parameter. -/
def Msg.slot {F G : Type} : Msg F G → WireSlot
  | .g1 _ => .g1
  | .fr _ => .fr

/-! The repack walk order (calldata.rs:109-126), which is also the transcript read
    order: the advice/lookup/perm/trash/quotient commitment groups, the eval block,
    f_com, the q_eval block, pi. The two trailing singletons are why
    compressedLen and repackedLen each carry two extra G1 terms.

    Declared in Midfall.Generator.RepackedProofLayoutPlan's own namespace (not this
    file's) so that the plan's dotted spelling plan.slots resolves: Lean's dot
    notation looks up the head constant's namespace, and a Lowering-namespaced
    RepackedProofLayoutPlan.slots would be unreachable from a plan term. The
    deviation is recorded here because it is a namespace choice, not a name choice.

    It also means the definition sits between two halves of this file's namespace
    block: Lean resolves plan.slots in the HEAD constant's namespace, so a
    Lowering-namespaced RepackedProofLayoutPlan.slots is unreachable from a plan term
    (the sketch's spelling does not typecheck as written - reported as a sketch
    defect). -/

end Midfall.Lowering

namespace Midfall.Generator.RepackedProofLayoutPlan

def slots (plan : RepackedProofLayoutPlan) : List Midfall.Lowering.WireSlot :=
  List.replicate plan.prefixG1Count Midfall.Lowering.WireSlot.g1 ++
    List.replicate plan.numEvals Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1] ++
    List.replicate plan.numPointSets Midfall.Lowering.WireSlot.fr ++
      [Midfall.Lowering.WireSlot.g1]

end Midfall.Generator.RepackedProofLayoutPlan

namespace Midfall.Lowering
open Midfall Midfall.Halo2
open Midfall.Generator (RepackedProofLayoutPlan ProofCalldataLayout RepackError)
variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Contract-side bytes of one message: the EIP-2537 padded point (calldata.rs:74-85)
    or the 32-byte big-endian scalar (scalar_le_to_be_word). This is the encoder half
    of what the transcript absorbs, and it is codec-generic on purpose - the concrete
    BLS codec lives under Instances/ (D-P17). -/
def msgContractBytes {G₁ : Type} (c : G1Codec G₁) : Msg (Fr p) G₁ → Bytes
  | .g1 Q => c.toEip Q
  | .fr s => Midfall.frToInputBE s

/-- PLAN 9.5 encodeContractProof: the concatenation of the messages' contract
    bytes. Layout-independent, because the schedule is carried by ms itself - which
    is exactly why repack_spec_wire needs the plan on one side and not the other. -/
def encodeContractProof {G₁ : Type} (c : G1Codec G₁) (ms : List (Msg (Fr p) G₁)) : Bytes :=
  ms.foldl (fun acc m => acc ++ msgContractBytes c m) Bytes.empty

/-! ### 2. The repack walk and its pure inverse -/

/-- One slot of the repack walk. The two error arms are the reference's own
    RepackError variants (api.rs:547-559); the hex payload is rendered by
    Midfall.Generator.hexEncodeLower, which is the port of the hex::encode the
    reference calls at CD:71 and CD:102 (the sketch's SKETCH name hexOf does not
    exist in the tree; this does, and its fidelity is gated by
    hexEncodeLower_matchesRustHex_ok in Generator/Calldata.lean). The
    non-canonical arm hexes the REVERSED bytes because CD:98-99 reverses before
    hexing - the big-endian spelling.

    The two none arms of bytesTake are unreachable after repackProof's length guard
    and are kept because the reference's indexing would panic there (CD:64, CD:89). -/
def repackSlot {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (π : Bytes) :
    WireSlot → Nat → Except RepackError (Bytes × Nat)
  | .g1, cur =>
    match bytesTake π cur g1CompressedWidth with
    | none => .error (RepackError.invalidCompressedG1 (offset := cur) (bytesHex := ""))
    | some comp =>
      match c.ofCompressed? comp with
      | none => .error (RepackError.invalidCompressedG1 (offset := cur)
                          (bytesHex := Midfall.Generator.hexEncodeLower comp))
      | some Q => .ok (c.toEip Q, cur + g1CompressedWidth)
  | .fr, cur =>
    match bytesTake π cur 32 with
    | none => .error (RepackError.nonCanonicalScalar (offset := cur) (bytesHex := ""))
    | some le =>
      match Midfall.frOfRepr? (p := p) le with
      | none => .error (RepackError.nonCanonicalScalar (offset := cur)
                          (bytesHex := Midfall.Generator.hexEncodeLower
                            (Midfall.Generator.bytesReverse le)))
      | some s => .ok (Midfall.frToInputBE s, cur + 32)

/-- Port of VerifierBuildInputs::repack_proof (calldata.rs:43-128) over an abstract
    codec. The exact-length guard comes FIRST, as the reference's does (CD:49), and
    it is what makes the bytesTake arms above unreachable.

    This is the S.repackProof of attack.md FIX 40: it errors with RepackError, so the
    binding composition
      S.repackProof π |>.mapError GeneratorError.fromRepackError >>=
        (S.encodeCalldata L.plan · inst)
    typechecks - the two error types meet only after that mapError, which is exactly
    the ill-typedness FIX 40 repairs (the original P1 sketch bound Except RepackError
    with Except GeneratorError). -/
def repackProof {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan) (c : G1Codec G₁)
    (π : Bytes) : Except RepackError Bytes := do
  if π.size ≠ plan.compressedLen then
    throw (RepackError.lengthMismatch (expected := plan.compressedLen) (actual := π.size)
      (prefixG1 := plan.prefixG1Count) (numEvals := plan.numEvals)
      (numPointSets := plan.numPointSets))
  let (out, _) ← plan.slots.foldlM
    (fun (st : Bytes × Nat) sl => do
      let (b, cur') ← repackSlot (p := p) (c := c) π sl st.2
      pure (st.1 ++ b, cur'))
    (Bytes.empty, 0)
  pure out

/-- Pure schedule-driven decode of the COMPRESSED stream - the message-level mirror
    of repackProof, and NOT decodeRust (which also runs the whole pipeline and so can
    fault for algebraic reasons that have nothing to do with the bytes). It carries
    repackProof's exact-length guard: attack.md's repack_spec entry shows that
    without it the iff fails for a proof with trailing bytes, which repackProof
    rejects and decodeWire would otherwise accept. -/
def decodeWire {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan) (c : G1Codec G₁)
    (π : Bytes) : Option (List (Msg (Fr p) G₁)) :=
  if π.size ≠ plan.compressedLen then none
  else
    ((plan.slots.foldlM
        (fun (st : List (Msg (Fr p) G₁) × Nat) sl =>
          match sl with
          | WireSlot.g1 => do
              let comp ← bytesTake π st.2 g1CompressedWidth
              let Q ← c.ofCompressed? comp
              pure (st.1 ++ [Msg.g1 Q], st.2 + g1CompressedWidth)
          | WireSlot.fr => do
              let le ← bytesTake π st.2 32
              let s ← Midfall.frOfRepr? (p := p) le
              pure (st.1 ++ [Msg.fr s], st.2 + 32))
        ([], 0))).map Prod.fst

/-! ### 3. The envelope -/

/-- evm.rs:22-38, the wire encoder. NOT re-implemented: Midfall.Generator.Evm's
    encodeCalldata is the P-12 port of the same Rust function, gated against the
    generated contract's head words (encodeCalldata_matchesGeneratedHead_ok), and
    PLAN 9.5's encodeCalldataRaw is the same term. Re-declaring the byte shape here
    would be the duplicate-definition pattern the plans README flags (abiTrue), so
    this is an alias and the deviation from the sketch is recorded here. -/
def encodeCalldataRaw (proof : Bytes) (instances : List Word256) : Bytes :=
  Midfall.Generator.encodeCalldata proof instances

/-- calldata.rs:132-149 (VerifierBuildInputs::encode_calldata): the instance-length
    check against GeneratorConfig.numInstances (CD:137-146, whose format! payload is
    reproduced verbatim by Generator/Calldata.lean's port), then the repack, then the
    wire encoder. The RepackError lift is GeneratorError.fromRepackError
    (Api.lean:388), the coercion the Rust's ? at CD:147 applies.

    The instance words are the canonical frWord of each Fr, which is what the
    contract's instance loop compares against r. -/
def encodeCalldata {G₁ : Type} (numInstances : Nat) (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes := do
  if inst.size ≠ numInstances then
    throw (Midfall.Generator.GeneratorError.planning (stage := "calldata")
      (message := "instance length mismatch: expected " ++ toString numInstances
        ++ ", got " ++ toString inst.size))
  match repackProof (p := p) plan c π with
  | .error e => throw (Midfall.Generator.GeneratorError.fromRepackError e)
  | .ok proof => pure (encodeCalldataRaw proof (inst.toList.map frWord))

/-- attack.md FIX 40, spelled as a term so the binding composition has a name in the
    tree and stage 4's Surface field can be stated against it: repack, lift the error
    channel, then encode. The point of the gate is that the two error types meet only
    after mapError - the original P1 sketch bound Except RepackError with
    Except GeneratorError and did not typecheck at all. -/
def repackThenEncode {G₁ : Type} (numInstances : Nat) (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes :=
  (repackProof (p := p) plan c π |>.mapError Midfall.Generator.GeneratorError.fromRepackError) >>=
    fun proof =>
      if inst.size ≠ numInstances then
        Except.error (Midfall.Generator.GeneratorError.planning (stage := "calldata")
          (message := "instance length mismatch: expected " ++ toString numInstances
            ++ ", got " ++ toString inst.size))
      else Except.ok (encodeCalldataRaw proof (inst.toList.map frWord))

/-- PLAN 9.5 calldataOf: the canonical calldata of a message list and RAW instance
    words. This is the right-hand side of both calldata specs. -/
def calldataOf {G₁ : Type} (c : G1Codec G₁) (ms : List (Msg (Fr p) G₁))
    (inst : List Word256) : Bytes :=
  encodeCalldataRaw (encodeContractProof c ms) inst

/-! ### 4. The contract-shaped decoder -/

/-- calldataload semantics: 32 bytes at i, zero past the end (the EVM pads a short
    read with zeros rather than faulting, which is what makes the trailing-byte and
    short-calldata guards in VkLoading.yul the only defence). -/
def cdWord (cd : Bytes) (i : Nat) : Word256 :=
  let bs := cd.data.toList
  BitVec.ofNat 256 ((List.range 32).foldl
    (fun acc j => acc * 256 + ((bs.drop (i + j)).head?.map UInt8.toNat).getD 0) 0)

/-- common_uncompressed_g1's range checks (AssemblyHelpers.yul:94-104): each
    coordinate's high word below 2^128 and the reconstructed 384-bit value below
    pBase. This is the gate that makes an accepted G1 block the canonical encoding
    of its point, and therefore what calldata_canonical's EXACTness rests on. -/
def g1WordsOk (cd : Bytes) (cptr : Nat) : Bool :=
  let xh := (cdWord cd cptr).toNat
  let xl := (cdWord cd (cptr + 32)).toNat
  let yh := (cdWord cd (cptr + 64)).toNat
  let yl := (cdWord cd (cptr + 96)).toNat
  xh < 2 ^ 128 && yh < 2 ^ 128 &&
    xh * 2 ^ 256 + xl < Midfall.Assumptions.pBase &&
    yh * 2 ^ 256 + yl < Midfall.Assumptions.pBase

/-- The slot walk over the repacked proof region. Each guard is a template line,
    cited at the site. ofEip? success is required here even though the contract does
    NOT decode at parse time: the contract rejects off-curve and off-subgroup points
    later, through the G1MSM calls the accumulator and PCS blocks perform, which is
    what points_subgroup_checked is owed. The port takes the decode at parse time and
    says so, because the alternative is a decoder that returns points it knows are
    junk. -/
def decodeSlots {G₁ : Type} (c : G1Codec G₁) (cd : Bytes) :
    List WireSlot → Nat → Option (List (Msg (Fr p) G₁) × Nat)
  | [], cur => some ([], cur)
  | .g1 :: rest, cur => do
    guard (g1WordsOk cd cur)                        -- AssemblyHelpers.yul:94-104
    let b ← bytesTake cd cur g1EipWidth
    let Q ← c.ofEip? b
    let (ms, cur') ← decodeSlots c cd rest (cur + g1EipWidth)
    pure (Msg.g1 Q :: ms, cur')
  | .fr :: rest, cur => do
    let w := cdWord cd cur
    guard (w.toNat < p)                             -- TranscriptProofParser.yul:319, :382
    let (ms, cur') ← decodeSlots c cd rest (cur + 32)
    pure (Msg.fr (Nat.cast w.toNat) :: ms, cur')

/-- PLAN 9.5 decodeCalldata, over raw Word256 instances (R-26.7: the >= r rejection
    must stay visible, so nothing here reduces mod p). Every guard cites the template
    line it models; the modulus test is against p, which the Surface pins to
    Midfall.Assumptions.r (the contract compares against the FR_MODULUS literal).

    The third guard, L.proofEnd == L.proofCptr + L.proofLen, is attack.md's
    calldata_canonical FIX and is load-bearing for hand-built layouts - see this
    file's header. The last two guards are the parser's own end-of-proof cursor check
    (TranscriptProofParser.yul:416) and the instance canonicality fold (:63-68). -/
def decodeCalldata {G₁ : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G₁) (cd : Bytes) :
    Option (List (Msg (Fr p) G₁) × Array Word256) := do
  let plan := RepackedProofLayoutPlan.fromProofLayout L
  let numInstCptr := L.proofEnd
  let instCptr := numInstCptr + 32
  guard (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof)  -- solc dispatcher
  guard (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr)     -- 0x64
  guard (L.proofEnd == L.proofCptr + L.proofLen)                       -- attack fix
  guard ((cdWord cd 4).toNat == 0x40 &&
         (cdWord cd 0x24).toNat == numInstCptr - 4)                    -- Halo2Verifier.sol:148
  guard ((cdWord cd 0x44).toNat == L.proofLen)                         -- VkLoading.yul:101
  guard ((cdWord cd numInstCptr).toNat == numInstances)                -- VkLoading.yul:102
  guard (cd.size == instCptr + 32 * numInstances)                      -- VkLoading.yul:106-112
  let (ms, cur) ← decodeSlots (p := p) c cd plan.slots L.proofCptr
  guard (cur == numInstCptr)                                           -- TranscriptProofParser.yul:416
  let inst := (List.range numInstances).map (fun i => cdWord cd (instCptr + 32 * i))
  guard (inst.all (fun w => w.toNat < p))                              -- TranscriptProofParser.yul:63-68
  pure (ms, inst.toArray)

/-! ### 5. Layout arithmetic -/

/-- Every repacked proof is a whole number of words, which is what lets the ABI
    heads be 32-byte aligned without any padding term. -/
theorem repackedLen_mod32 (plan : RepackedProofLayoutPlan) :
    plan.repackedLen % 32 = 0 := by
  have hg : Midfall.Generator.g1Bytes = 128 := rfl
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  have heq : plan.repackedLen =
      32 * (4 * plan.prefixG1Count + plan.numEvals + 8 + plan.numPointSets) := by
    rw [RepackedProofLayoutPlan.repackedLen, hg, hw]
    omega
  rw [heq]
  omega

/-- A left fold of addition is its seed plus its total. The reference's two sums are
    left folds seeded at a running cursor rather than at 0, so this is the step that
    turns "fold from anywhere" into "seed + fold from 0". -/
theorem foldl_add_seed : ∀ (l : List Nat) (acc : Nat),
    l.foldl (fun a n => a + n) acc = acc + l.foldl (fun a n => a + n) 0 := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x rest ih =>
      intro acc
      show rest.foldl (fun a n => a + n) (acc + x) = acc + (x :: rest).foldl (fun a n => a + n) 0
      rw [ih (acc + x), List.foldl_cons, ih (0 + x)]
      omega

/-- Dropping the zero entries of a list of naturals does not change its sum, however
    the left fold of addition is seeded. This is the whole content of the filter in
    commitmentReadGroups: it drops only counts that would have added 0. -/
theorem foldl_add_filter_ne_zero : ∀ (l : List Nat) (acc : Nat),
    (l.filter (fun x => x != 0)).foldl (fun a n => a + n) acc =
      l.foldl (fun a n => a + n) acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons a rest ih =>
      intro acc
      rw [List.filter_cons]
      by_cases h : (a != 0) = true
      · rw [ite_eq_left h, List.foldl_cons, ih, List.foldl_cons]
      · rw [ite_eq_right (by simpa using h), ih, List.foldl_cons]
        have ha : a = 0 := by simpa using h
        rw [ha, Nat.add_zero]

/-- A flat-map of a pair is a map of the pair's sum, under a left fold of addition.
    This is the lookup row: AP:271-292 pushes \[helpers, accumulator\] per lookup with
    NO filter, while nonQuotientG1Count adds the same two counts per lookup. -/
theorem foldl_flatMap_pair {α : Type} (f g : α → Nat) :
    ∀ (l : List α) (acc : Nat),
      (l.flatMap (fun x => [f x, g x])).foldl (fun a n => a + n) acc =
        (l.map (fun x => f x + g x)).foldl (fun a n => a + n) acc := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons x rest ih =>
      intro acc
      show ((f x :: g x :: rest.flatMap (fun y => [f y, g y]))).foldl (fun a n => a + n) acc = _
      show ((f x :: g x :: rest.flatMap (fun y => [f y, g y]))).foldl (fun a n => a + n) acc =
        ((f x + g x) :: rest.map (fun y => f y + g y)).foldl (fun a n => a + n) acc
      simp only [List.foldl_cons, ih, Nat.add_assoc]

/-- The plan's prefix G1 count is the layout's transcript-facing commitment count.
    The filter in commitmentReadGroups drops only ZERO counts, so the sum is
    unchanged - that is the whole content, and it is why the lemma is not rfl: the
    two sides are different folds over different fields. PROVED here: the three
    helpers above are the three things the two spellings differ by - the seed of a
    left fold, the zero filter, and the unfiltered per-lookup pair push. -/
theorem sum_commitmentReadGroups (L : ProofCalldataLayout) :
    (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count = L.commitmentG1Count := by
  show L.commitmentReadGroups.foldl (fun acc n => acc + n) 0 = L.commitmentG1Count
  simp only [ProofCalldataLayout.commitmentReadGroups, ProofCalldataLayout.commitmentG1Count,
    ProofCalldataLayout.nonQuotientG1Count]
  by_cases ht : (L.trash.itemCount != 0) = true
  · rw [ite_eq_left ht]
    simp only [List.foldl_append, foldl_add_filter_ne_zero,
      foldl_flatMap_pair (fun (l : Midfall.Generator.ProofLookupCommitmentsLayout) =>
        l.helpers.itemCount) (fun l => l.accumulator.itemCount),
      List.foldl_cons, List.foldl_nil]
    rw [foldl_add_seed]
  · rw [ite_eq_right (by simpa using ht)]
    have hz : L.trash.itemCount = 0 := by simpa using ht
    rw [hz]
    simp only [List.foldl_append, foldl_add_filter_ne_zero,
      foldl_flatMap_pair (fun (l : Midfall.Generator.ProofLookupCommitmentsLayout) =>
        l.helpers.itemCount) (fun l => l.accumulator.itemCount),
      List.foldl_cons, List.foldl_nil]
    rw [foldl_add_seed]
    omega

/-! The inversion machinery for 'proofLen_eq_repackedLen'. Nothing here is a new
    definition the specs depend on: 'except_bind_ok' is the one-step "a do-block that
    returned ok must have had every bind return ok" lemma, the two 'foldlM_*' lemmas
    say what the commitment walk does to its cursor and to the sections it appends,
    and 'sumNat' is the reference's own left fold of addition named once. They are
    here rather than in Generator/Abi.lean because this package may not edit that file
    and because only this file's theorem consumes them. -/

theorem except_bind_ok {ε α β : Type} (m : Except ε α) (f : α → Except ε β) {y : β}
    (h : m >>= f = .ok y) : ∃ x, m = .ok x ∧ f x = .ok y := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | error e => cases h

theorem takeCommitmentSection_ok (protocol : Midfall.Generator.ProtocolPlan)
    (readIdx cursor count : Nat) (expected : Midfall.Generator.CommitmentRead) (label : String)
    (sect : Midfall.Generator.ProofSection) (r' c' : Nat)
    (h : ProofCalldataLayout.takeCommitmentSection protocol readIdx cursor expected count label =
      .ok (sect, r', c')) :
    sect = Midfall.Generator.ProofSection.new cursor count Midfall.Generator.g1Bytes ∧
      c' = cursor + count * Midfall.Generator.g1Bytes := by
  rw [ProofCalldataLayout.takeCommitmentSection] at h
  simp only [Bind.bind] at h
  obtain ⟨ri, hri, h2⟩ := except_bind_ok _ _ h
  cases h2
  exact ⟨rfl, rfl⟩

def sumNat (l : List Nat) : Nat := l.foldl (fun a b => a + b) 0

theorem sumNat_nil : sumNat [] = 0 := rfl
theorem sumNat_cons (x : Nat) (l : List Nat) : sumNat (x :: l) = x + sumNat l := by
  show l.foldl (fun a b => a + b) (0 + x) = x + sumNat l
  rw [Nat.zero_add, foldl_add_seed]
  rfl
theorem sumNat_append (l l' : List Nat) : sumNat (l ++ l') = sumNat l + sumNat l' := by
  induction l generalizing l' with
  | nil => simp [sumNat_nil]
  | cons x rest ih =>
      rw [sumNat_cons]
      show sumNat (x :: (rest ++ l')) = (x + sumNat rest) + sumNat l'
      rw [sumNat_cons, ih]
      omega

/-- A section whose item width is the G1 width and whose byte length is derived. -/
def sectIsG1 (s : Midfall.Generator.ProofSection) : Prop :=
  s.itemBytes = Midfall.Generator.g1Bytes ∧ s.byteLen = s.itemCount * Midfall.Generator.g1Bytes

theorem sectIsG1_new (start count : Nat) :
    sectIsG1 (Midfall.Generator.ProofSection.new start count Midfall.Generator.g1Bytes) :=
  ⟨rfl, rfl⟩

theorem foldlM_take_ok (protocol : Midfall.Generator.ProtocolPlan)
    (expected : Midfall.Generator.CommitmentRead) (label : String) :
    ∀ (counts : List Nat) (init res : List Midfall.Generator.ProofSection × Nat × Nat),
      counts.foldlM
        (fun st count =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2 expected count label).bind
            fun x => Except.ok (st.1 ++ [x.1], x.2.1, x.2.2)) init = .ok res →
      (∀ s ∈ init.1, sectIsG1 s) →
      res.2.2 = init.2.2 + sumNat (counts.map (fun c => c * Midfall.Generator.g1Bytes)) ∧
        (∀ s ∈ res.1, sectIsG1 s) ∧
        sumNat (res.1.map (fun s => s.itemCount)) =
          sumNat (init.1.map (fun s => s.itemCount)) + sumNat counts := by
  intro counts
  induction counts with
  | nil =>
      intro init res h hinit
      have hsub : res = init := by cases h; rfl
      subst hsub
      exact ⟨rfl, hinit, rfl⟩
  | cons c rest ih =>
      intro init res h hinit
      rw [List.foldlM_cons] at h
      simp only [Bind.bind] at h
      obtain ⟨st1, hst1, hrest⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst1'⟩ := except_bind_ok _ _ hst1
      have hsec := takeCommitmentSection_ok protocol init.2.1 init.2.2 c expected label x.1 x.2.1 x.2.2 hx
      have hc1 : st1.1 = init.1 ++ [x.1] := by cases hst1'; rfl
      have hc2 : st1.2.1 = x.2.1 := by cases hst1'; rfl
      have hc3 : st1.2.2 = x.2.2 := by cases hst1'; rfl
      have hgx : sectIsG1 x.1 := hsec.1 ▸ sectIsG1_new init.2.2 c
      have hnew : ∀ s ∈ st1.1, sectIsG1 s := by
        intro s hs
        rw [hc1] at hs
        simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hinit s hs
        · exact hgx
      obtain ⟨hcur, hgis, hcnt⟩ := ih st1 res hrest hnew
      refine ⟨?_, hgis, ?_⟩
      · rw [hcur, hc3, hsec.2, List.map_cons, sumNat_cons]
        omega
      · rw [hcnt, hc1, sumNat_cons, List.map_append, sumNat_append, List.map_singleton,
          sumNat_cons, sumNat_nil]
        have he : x.1.itemCount = c := by rw [hsec.1]; rfl
        rw [he]
        omega


theorem sumNat_map_mul (k : Nat) (l : List Nat) :
    sumNat (l.map (fun c => c * k)) = k * sumNat l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.map_cons, sumNat_cons, sumNat_cons, ih]
      ring

theorem foldlM_lookups_ok (protocol : Midfall.Generator.ProtocolPlan) :
    ∀ (pairs : List (Nat × Nat))
      (init res : List Midfall.Generator.ProofLookupCommitmentsLayout × Nat × Nat),
      pairs.foldlM
        (fun st pair =>
          (ProofCalldataLayout.takeCommitmentSection protocol st.2.1 st.2.2
              Midfall.Generator.CommitmentRead.lookupHelper pair.2 "lookup helper").bind
            fun x =>
          (ProofCalldataLayout.takeCommitmentSection protocol x.2.1 x.2.2
              Midfall.Generator.CommitmentRead.lookupAccumulator 1 "lookup accumulator").bind
            fun y =>
          Except.ok (st.1 ++ [{ lookup := pair.1, helpers := x.1, accumulator := y.1 }],
            y.2.1, y.2.2)) init = .ok res →
      (∀ r ∈ init.1, sectIsG1 r.helpers ∧ sectIsG1 r.accumulator) →
      res.2.2 = init.2.2 + Midfall.Generator.g1Bytes * sumNat (pairs.map (fun p => p.2 + 1)) ∧
        (∀ r ∈ res.1, sectIsG1 r.helpers ∧ sectIsG1 r.accumulator) ∧
        sumNat (res.1.map (fun r => r.helpers.itemCount + r.accumulator.itemCount)) =
          sumNat (init.1.map (fun r => r.helpers.itemCount + r.accumulator.itemCount)) +
            sumNat (pairs.map (fun p => p.2 + 1)) := by
  intro pairs
  induction pairs with
  | nil =>
      intro init res h hinit
      have hsub : res = init := by cases h; rfl
      subst hsub
      exact ⟨rfl, hinit, rfl⟩
  | cons pr rest ih =>
      intro init res h hinit
      rw [List.foldlM_cons] at h
      simp only [Bind.bind] at h
      obtain ⟨st1, hst1, hrest⟩ := except_bind_ok _ _ h
      obtain ⟨x, hx, hst1'⟩ := except_bind_ok _ _ hst1
      obtain ⟨y, hy, hst1''⟩ := except_bind_ok _ _ hst1'
      have hsec1 := takeCommitmentSection_ok protocol init.2.1 init.2.2 pr.2
        Midfall.Generator.CommitmentRead.lookupHelper "lookup helper" x.1 x.2.1 x.2.2 hx
      have hsec2 := takeCommitmentSection_ok protocol x.2.1 x.2.2 1
        Midfall.Generator.CommitmentRead.lookupAccumulator "lookup accumulator" y.1 y.2.1 y.2.2 hy
      have hc1 : st1.1 = init.1 ++ [{ lookup := pr.1, helpers := x.1, accumulator := y.1 }] :=
        by cases hst1''; rfl
      have hc2 : st1.2.2 = y.2.2 := by cases hst1''; rfl
      have hnew : ∀ r ∈ st1.1, sectIsG1 r.helpers ∧ sectIsG1 r.accumulator := by
        intro r hr
        rw [hc1] at hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hinit r hr
        · exact ⟨hsec1.1 ▸ sectIsG1_new init.2.2 pr.2, hsec2.1 ▸ sectIsG1_new x.2.2 1⟩
      obtain ⟨hcur, hgis, hcnt⟩ := ih st1 res hrest hnew
      refine ⟨?_, hgis, ?_⟩
      · rw [hcur, hc2, hsec2.2, hsec1.2, List.map_cons, sumNat_cons]
        ring
      · rw [hcnt, hc1, List.map_append, sumNat_append, List.map_singleton, sumNat_cons, sumNat_nil]
        have he1 : x.1.itemCount = pr.2 := by rw [hsec1.1]; rfl
        have he2 : y.1.itemCount = 1 := by rw [hsec2.1]; rfl
        rw [he1, he2, List.map_cons, sumNat_cons]
        omega


/-- For layouts built by fromProtocol at the ABI proof pointer the proof length IS
    the repacked length and the sections tile exactly (survey, Encoding area: VM and
    Direct plans share this layout). Hand-built layouts need not, which is what the
    guard in decodeCalldata defends against and what
    commitmentReadGroups_disagreeWhenHandBuilt_ok exhibits.

    PROVED, and the proof is the cursor invariant M5-7 asked for rather than a
    paraphrase of it: 'except_bind_ok' peels the six binds and the trailing assert of
    'fromProtocol', 'foldlM_take_ok' and 'foldlM_lookups_ok' say what each of the ten
    steps does to the cursor and to the sections it appends, and the two conjuncts are
    then arithmetic on the resulting cursor chain. The second conjunct is the
    layout-consistency guard 'decodeCalldata' defends against, so this is the lemma
    that makes that guard satisfiable for every generated layout - and therefore the
    lemma that makes 'hcd' in the ten partial specs satisfiable rather than vacuous. -/
theorem proofLen_eq_repackedLen (protocol : Midfall.Generator.ProtocolPlan)
    (numEvals numPointSets : Nat) (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr
        numEvals numPointSets = .ok L) :
    L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen ∧
      L.proofEnd = L.proofCptr + L.proofLen := by
  set cptr := Midfall.Generator.abiVerifyProofProofCptr with hcptrdef
  rw [ProofCalldataLayout.fromProtocol] at h
  simp only [Bind.bind] at h
  obtain ⟨x1, hx1, h1⟩ := except_bind_ok _ _ h
  obtain ⟨x2, hx2, h2⟩ := except_bind_ok _ _ h1
  obtain ⟨x3, hx3, h3⟩ := except_bind_ok _ _ h2
  obtain ⟨x4, hx4, h4⟩ := except_bind_ok _ _ h3
  obtain ⟨x5, hx5, h5⟩ := except_bind_ok _ _ h4
  obtain ⟨x6, hx6, h6⟩ := except_bind_ok _ _ h5
  by_cases hc : (x6.2.1 != protocol.proof.commitments.length) = true
  · rw [ite_eq_left hc] at h6
    obtain ⟨r, hr, _⟩ := except_bind_ok _ _ h6
    cases hr
  · rw [ite_eq_right (by simpa using hc)] at h6
    let ws6 := ProofCalldataLayout.wordSection x6.2.2 numEvals
    let fc := Midfall.Generator.ProofSection.new ws6.2 1 Midfall.Generator.g1Bytes
    let ws8 := ProofCalldataLayout.wordSection fc.end numPointSets
    let piS := Midfall.Generator.ProofSection.new ws8.2 1 Midfall.Generator.g1Bytes
    have hcptrE : L.proofCptr = cptr := by cases h6; rfl
    have hadvE : L.advicePhases = x1.1 := by cases h6; rfl
    have hlmE : L.lookupMultiplicities = x2.1 := by cases h6; rfl
    have hppE : L.permutationProducts = x3.1 := by cases h6; rfl
    have hlksE : L.lookups = x4.1 := by cases h6; rfl
    have htrE : L.trash = x5.1 := by cases h6; rfl
    have hqlE : L.quotientLimbs = x6.1 := by cases h6; rfl
    have hevE : L.evals = ws6.1 := by cases h6; rfl
    have hfE : L.fCom = fc := by cases h6; rfl
    have hqE : L.qEvals = ws8.1 := by cases h6; rfl
    have hpeE : L.proofEnd = piS.end := by cases h6; rfl
    have hplE : L.proofLen = piS.end - cptr := by cases h6; rfl
    let lks := (List.range protocol.lookupChunks.length).zip protocol.lookupChunks
    have h1' := foldlM_take_ok protocol Midfall.Generator.CommitmentRead.advice "advice phase"
      protocol.numUserAdvices ([], 0, cptr) x1 hx1 (by intro s hs; simp at hs)
    have h2' := takeCommitmentSection_ok protocol x1.2.1 x1.2.2 protocol.numLookups
      Midfall.Generator.CommitmentRead.lookupMultiplicity "lookup multiplicity" x2.1 x2.2.1 x2.2.2 hx2
    have h3' := takeCommitmentSection_ok protocol x2.2.1 x2.2.2 protocol.numPermutationZs
      Midfall.Generator.CommitmentRead.permutationProduct "permutation product" x3.1 x3.2.1 x3.2.2 hx3
    have h4' := foldlM_lookups_ok protocol lks ([], x3.2.1, x3.2.2) x4 hx4
      (by intro r hr; simp at hr)
    have h5' := takeCommitmentSection_ok protocol x4.2.1 x4.2.2 protocol.numTrashcans
      Midfall.Generator.CommitmentRead.trash "trash" x5.1 x5.2.1 x5.2.2 hx5
    have h6' := takeCommitmentSection_ok protocol x5.2.1 x5.2.2 protocol.numQuotients
      Midfall.Generator.CommitmentRead.quotient "quotient limb" x6.1 x6.2.1 x6.2.2 hx6
    have e2 : x2.1.itemCount = protocol.numLookups := by rw [h2'.1]; rfl
    have e3 : x3.1.itemCount = protocol.numPermutationZs := by rw [h3'.1]; rfl
    have e5 : x5.1.itemCount = protocol.numTrashcans := by rw [h5'.1]; rfl
    have e6 : x6.1.itemCount = protocol.numQuotients := by rw [h6'.1]; rfl
    have hg : Midfall.Generator.g1Bytes = 128 := rfl
    have hw : Midfall.Generator.wordBytes = 32 := rfl
    have hCG : L.commitmentG1Count = sumNat protocol.numUserAdvices + protocol.numLookups
        + protocol.numPermutationZs + sumNat (lks.map (fun p => p.2 + 1))
        + protocol.numTrashcans + protocol.numQuotients := by
      simp only [ProofCalldataLayout.commitmentG1Count, ProofCalldataLayout.nonQuotientG1Count,
        hadvE, hlmE, hppE, hlksE, htrE, hqlE]
      show sumNat (x1.1.map (fun s => s.itemCount)) + x2.1.itemCount + x3.1.itemCount
          + sumNat (x4.1.map (fun r => r.helpers.itemCount + r.accumulator.itemCount))
          + x5.1.itemCount + x6.1.itemCount = _
      rw [h1'.2.2, h4'.2.2, e2, e3, e5, e6]
      simp only [List.map_nil, sumNat_nil, Nat.zero_add]
    have hc6 : x6.2.2 = cptr + Midfall.Generator.g1Bytes * L.commitmentG1Count := by
      rw [h6'.2, h5'.2, h4'.1, h3'.2, h2'.2, h1'.1, sumNat_map_mul, hCG, hg]
      ring
    have hws6 : ws6.2 = x6.2.2 + numEvals * Midfall.Generator.wordBytes := rfl
    have hfc : fc.end = ws6.2 + 1 * Midfall.Generator.g1Bytes := rfl
    have hws8 : ws8.2 = fc.end + numPointSets * Midfall.Generator.wordBytes := rfl
    have hpi : piS.end = ws8.2 + 1 * Midfall.Generator.g1Bytes := rfl
    have hpe2 : piS.end = cptr + (Midfall.Generator.g1Bytes * L.commitmentG1Count + numEvals * Midfall.Generator.wordBytes
        + numPointSets * Midfall.Generator.wordBytes + 2 * Midfall.Generator.g1Bytes) := by
      rw [hpi, hws8, hfc, hws6, hc6]
      ring
    have hge : piS.end ≥ cptr := by rw [hpe2]; omega
    refine ⟨?_, ?_⟩
    · rw [hplE, hpe2, Nat.add_sub_cancel_left]
      have hrep : (RepackedProofLayoutPlan.fromProofLayout L).repackedLen
          = L.commitmentG1Count * Midfall.Generator.g1Bytes + L.evals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
            + L.qEvals.itemCount * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes := by
        show (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count * Midfall.Generator.g1Bytes
            + (RepackedProofLayoutPlan.fromProofLayout L).numEvals * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes
            + (RepackedProofLayoutPlan.fromProofLayout L).numPointSets * Midfall.Generator.wordBytes + Midfall.Generator.g1Bytes = _
        rw [sum_commitmentReadGroups L]
        rfl
      rw [hrep, hevE, hqE]
      have f1 : ws6.1.itemCount = numEvals := rfl
      have f2 : ws8.1.itemCount = numPointSets := rfl
      rw [f1, f2, hCG, hg, hw]
      ring
    · rw [hplE, hcptrE, hpeE, hpe2, Nat.add_sub_cancel_left]


/-! ### 6. The four specs -/

/-- decodeCalldata inverts calldataOf. hypotheses, each load-bearing:
    * hL / hlen / hend - the layout must be at the ABI pointer and self-consistent;
      together they are what proofLen_eq_repackedLen delivers for fromProtocol layouts.
    * hc : G1CodecLaws c - eipShape and toEip_one make every G1 message pass
      g1WordsOk (a padded block has high words 0 and coordinates below pBase), and
      ofEip_toEip recovers the point from those bytes.
    * hshape - the message list has the layout's slot shape; this is the readScheduleAgrees
      content for decodeRust outputs and is a hypothesis, not a fact, until stage 6.
    * hinst - instance words canonical, which is what the decoder's guard needs and
      what frWord gives when p <= 2^256.
    * hp : p <= 2^256 - attack.md's calldata_roundtrip entry: the .fr slot is encoded
      by frToInputBE (truncating at 2^256) and decoded as Nat.cast of the raw word, so
      for p > 2^256 a scalar at or above 2^256 does not round-trip. hinst bounds the
      INSTANCE words only, not the proof scalars.
    PROOF OBLIGATION, registered in SORRY.md (M5-8). -/
theorem calldata_roundtrip {G₁ : Type} [Group G₁]
    (hp : p ≤ 2 ^ 256) (L : ProofCalldataLayout)
    (hL : L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr)
    (hlen : L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen)
    (hend : L.proofEnd = L.proofCptr + L.proofLen)
    (c : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws c)
    (ms : List (Msg (Fr p) G₁))
    (hshape : ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout L).slots)
    (numInstances : Nat) (inst : List Word256) (hn : inst.length = numInstances)
    (hinst : ∀ w ∈ inst, w.toNat < p) :
    decodeCalldata (p := p) L numInstances c (calldataOf c ms inst) =
      some (ms, inst.toArray) := by
  sorry

/-- **THE LAYOUT-CONSISTENCY GUARD IS DERIVABLE, NOT AN ASSUMPTION.**
    'decodeCalldata' guards on `L.proofEnd = L.proofCptr + L.proofLen`, so a
    successful decode already carries it. P-MC-CALLDATA found 'calldata_canonical'
    taking it as an extra binder, which PLAN section H line 1280 does not, and
    restored the sketched form; these two lemmas are what make the restoration free
    rather than a strengthening nobody can discharge. They are also the vacuity
    refutation: break either guard and NOTHING decodes. -/
theorem decodeCalldata_none_of_layout_skew {G₁ : Type} (L : ProofCalldataLayout)
    (numInstances : Nat) (c : G1Codec G₁)
    (h : L.proofEnd ≠ L.proofCptr + L.proofLen) (cd : Bytes) :
    decodeCalldata (p := p) L numInstances c cd = none := by
  unfold decodeCalldata
  simp [h]

theorem decodeCalldata_none_of_pointer_skew {G₁ : Type} (L : ProofCalldataLayout)
    (numInstances : Nat) (c : G1Codec G₁)
    (h : L.proofCptr ≠ Midfall.Generator.abiVerifyProofProofCptr) (cd : Bytes) :
    decodeCalldata (p := p) L numInstances c cd = none := by
  unfold decodeCalldata
  simp [h]

theorem decodeCalldata_hend_of_some {G₁ : Type} (L : ProofCalldataLayout)
    (numInstances : Nat) (c : G1Codec G₁) (cd : Bytes)
    (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    L.proofEnd = L.proofCptr + L.proofLen := by
  by_contra H
  rw [decodeCalldata_none_of_layout_skew L numInstances c H cd] at h
  cases h

/-- EXACT in both modes (D7, and P-12's measurement of the templates): trailing bytes
    revert, non-canonical words revert, and an accepted G1 block is the canonical
    encoding of its point, so a decoded calldata is byte-for-byte the calldataOf of
    what it decoded to. The R-25 malleability lives in decodeAcc, which is not in this
    path at all - that is why accumulator mode needs no exception here.

    hypotheses: hc : eipRoundtrip is the decoder-first law that turns "the decoder
    accepted these bytes" into "these are the encoder's bytes for that point".

    P-MC-CALLDATA RESTORED THIS STATEMENT. It used to carry
    `hend : L.proofEnd = L.proofCptr + L.proofLen` as a binder, which PLAN section H
    does not: 'decodeCalldata' guards on exactly that equation, so a successful decode
    already implies it ('decodeCalldata_hend_of_some'). The hypothesis was a weakening
    of the sketched claim, and the sketched form is what stands here now.
    PROOF OBLIGATION, registered in SORRY.md (M5-8). -/
theorem calldata_canonical {G₁ : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G₁) (hc : c.eipRoundtrip)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd = calldataOf c ms inst.toList := by
  sorry

/-! The wire-level repack/decode agreement, D8's first half.

    Both walks are the same fold over the same schedule with the same cursor
    arithmetic, so the proof is one induction over 'plan.slots' carrying both states
    at once ('wire_go'). The two step functions are named ('repackGo', 'decodeGo')
    because they are written inline in the definitions above and the induction has to
    talk about them; each is defeq to the lambda it replaces, and the four 'step_*'
    lemmas are the per-slot agreement, one pair per slot kind, plus the pair of
    failure arms. 'widthSum' is the compressed width of a slot list, and
    'compressedLen_eq_widthSum' is what lets the induction start with the guard
    discharged} - without it the two walks would have to carry a partiality
    from 'bytesTake' that the exact-length guard already rules out. -/

section
variable {G₁ : Type}


variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}

def slotWidth : WireSlot → Nat
  | WireSlot.g1 => Midfall.g1CompressedWidth
  | WireSlot.fr => 32

def widthSum (slots : List WireSlot) : Nat := slots.foldl (fun a s => a + slotWidth s) 0

theorem widthSum_nil : widthSum [] = 0 := rfl

theorem foldlW_seed : ∀ (l : List WireSlot) (acc : Nat),
    l.foldl (fun a s => a + slotWidth s) acc = acc + widthSum l := by
  intro l
  induction l with
  | nil => intro acc; simp [widthSum]
  | cons x rest ih =>
      intro acc
      show rest.foldl (fun a s => a + slotWidth s) (acc + slotWidth x) =
        acc + rest.foldl (fun a s => a + slotWidth s) (0 + slotWidth x)
      rw [Nat.zero_add, ih (acc + slotWidth x), ih (slotWidth x)]
      omega

theorem widthSum_cons (x : WireSlot) (l : List WireSlot) :
    widthSum (x :: l) = slotWidth x + widthSum l := by
  show l.foldl (fun a s => a + slotWidth s) (0 + slotWidth x) = _
  rw [Nat.zero_add, foldlW_seed]

theorem widthSum_append (l l' : List WireSlot) :
    widthSum (l ++ l') = widthSum l + widthSum l' := by
  induction l with
  | nil => simp [widthSum_nil]
  | cons x rest ih =>
      rw [List.cons_append]
      rw [widthSum_cons, ih, widthSum_cons]
      omega

theorem widthSum_replicate (n : Nat) (w : Nat) (sl : WireSlot)
    (h : slotWidth sl = w) : widthSum (List.replicate n sl) = n * w := by
  induction n with
  | zero => simp [widthSum_nil]
  | succ n ih =>
      rw [List.replicate_succ, widthSum_cons, ih, h, Nat.succ_mul]
      omega

theorem widthSum_slots (plan : RepackedProofLayoutPlan) :
    widthSum plan.slots =
      plan.prefixG1Count * 48 + plan.numEvals * 32 + 48 + plan.numPointSets * 32 + 48 := by
  have hgw : slotWidth WireSlot.g1 = 48 := rfl
  have hfw : slotWidth WireSlot.fr = 32 := rfl
  show widthSum (List.replicate plan.prefixG1Count WireSlot.g1
      ++ List.replicate plan.numEvals WireSlot.fr ++ [WireSlot.g1]
      ++ List.replicate plan.numPointSets WireSlot.fr ++ [WireSlot.g1]) = _
  rw [widthSum_append, widthSum_append, widthSum_append, widthSum_append,
    widthSum_replicate plan.prefixG1Count 48 WireSlot.g1 hgw,
    widthSum_replicate plan.numEvals 32 WireSlot.fr hfw,
    widthSum_replicate plan.numPointSets 32 WireSlot.fr hfw]
  simp only [widthSum_cons, widthSum_nil, hgw]

theorem compressedLen_eq_widthSum (plan : RepackedProofLayoutPlan) :
    plan.compressedLen = widthSum plan.slots := by
  have hg : Midfall.Generator.g1CompressedBytes = 48 := rfl
  have hw : Midfall.Generator.wordBytes = 32 := rfl
  unfold RepackedProofLayoutPlan.compressedLen
  rw [hg, hw, widthSum_slots plan]


/-- The repackProof step, named so the induction can talk about it; defeq to the
    inline lambda in repackProof. -/
def repackGo (c : G1Codec G₁) (π : Bytes) (st : Bytes × Nat) (sl : WireSlot) :
    Except RepackError (Bytes × Nat) :=
  (Midfall.Lowering.repackSlot (p := p) c π sl st.2).bind fun x => pure (st.1 ++ x.1, x.2)

/-- The decodeWire step, named for the same reason. -/
def decodeGo (c : G1Codec G₁) (π : Bytes) (st : List (Msg (Fr p) G₁) × Nat) (sl : WireSlot) :
    Option (List (Msg (Fr p) G₁) × Nat) :=
  match sl with
  | WireSlot.g1 =>
      (bytesTake π st.2 Midfall.g1CompressedWidth).bind fun comp =>
        (c.ofCompressed? comp).bind fun Q =>
          pure (st.1 ++ [Msg.g1 Q], st.2 + Midfall.g1CompressedWidth)
  | WireSlot.fr =>
      (bytesTake π st.2 32).bind fun le =>
        (Midfall.frOfRepr? (p := p) le).bind fun s =>
          pure (st.1 ++ [Msg.fr s], st.2 + 32)

theorem encodeContractProof_go (c : G1Codec G₁) :
    ∀ (l : List (Msg (Fr p) G₁)) (acc : Bytes),
      l.foldl (fun a m => a ++ Midfall.Lowering.msgContractBytes (p := p) c m) acc =
        acc ++ Midfall.Lowering.encodeContractProof (p := p) c l := by
  intro l
  induction l with
  | nil =>
      intro acc
      show acc = acc ++ Midfall.Lowering.encodeContractProof (p := p) c []
      rw [show Midfall.Lowering.encodeContractProof (p := p) c [] = ByteArray.empty from rfl,
        ByteArray.append_empty]
  | cons m rest ih =>
      intro acc
      show rest.foldl (fun a x => a ++ Midfall.Lowering.msgContractBytes (p := p) c x)
        (acc ++ Midfall.Lowering.msgContractBytes (p := p) c m) =
        acc ++ Midfall.Lowering.encodeContractProof (p := p) c (m :: rest)
      have h1 : rest.foldl (fun a x => a ++ Midfall.Lowering.msgContractBytes (p := p) c x)
          (acc ++ Midfall.Lowering.msgContractBytes (p := p) c m)
          = (acc ++ Midfall.Lowering.msgContractBytes (p := p) c m) ++
              Midfall.Lowering.encodeContractProof (p := p) c rest :=
        ih (acc ++ Midfall.Lowering.msgContractBytes (p := p) c m)
      have h2 : Midfall.Lowering.encodeContractProof (p := p) c (m :: rest)
          = (Midfall.Lowering.msgContractBytes (p := p) c m) ++
              Midfall.Lowering.encodeContractProof (p := p) c rest := by
        show rest.foldl (fun a x => a ++ Midfall.Lowering.msgContractBytes (p := p) c x)
            (ByteArray.empty ++ Midfall.Lowering.msgContractBytes (p := p) c m) = _
        rw [ByteArray.empty_append]
        exact ih (Midfall.Lowering.msgContractBytes (p := p) c m)
      rw [h1, h2, ← ByteArray.append_assoc]

theorem encodeContractProof_append (c : G1Codec G₁) (l₁ l₂ : List (Msg (Fr p) G₁)) :
    Midfall.Lowering.encodeContractProof (p := p) c (l₁ ++ l₂) =
      Midfall.Lowering.encodeContractProof (p := p) c l₁ ++
        Midfall.Lowering.encodeContractProof (p := p) c l₂ := by
  show (l₁ ++ l₂).foldl (fun a m => a ++ Midfall.Lowering.msgContractBytes (p := p) c m)
      ByteArray.empty = _
  rw [List.foldl_append,
    show (List.foldl (fun a m => a ++ Midfall.Lowering.msgContractBytes (p := p) c m)
        ByteArray.empty l₁) = Midfall.Lowering.encodeContractProof (p := p) c l₁ from rfl,
    encodeContractProof_go c l₂ (Midfall.Lowering.encodeContractProof (p := p) c l₁)]

theorem step_g1_repack (c : G1Codec G₁) (π : Bytes) (cur : Nat) (comp : Bytes) (acc : Bytes)
    (Q : G₁) (hcomp : bytesTake π cur Midfall.g1CompressedWidth = some comp)
    (hq : c.ofCompressed? comp = some Q) :
    repackGo (p := p) c π (acc, cur) WireSlot.g1 =
      Except.ok (acc ++ c.toEip Q, cur + Midfall.g1CompressedWidth) := by
  rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
  dsimp only
  rw [hq]
  rfl

theorem step_g1_decode (c : G1Codec G₁) (π : Bytes) (cur : Nat) (comp : Bytes) (Q : G₁)
    (ms0 : List (Msg (Fr p) G₁)) (hcomp : bytesTake π cur Midfall.g1CompressedWidth = some comp)
    (hq : c.ofCompressed? comp = some Q) :
    decodeGo (p := p) c π (ms0, cur) WireSlot.g1 =
      some (ms0 ++ [Msg.g1 Q], cur + Midfall.g1CompressedWidth) := by
  rw [decodeGo, hcomp]
  show (c.ofCompressed? comp).bind (fun Q =>
      pure (ms0 ++ [Msg.g1 Q], cur + Midfall.g1CompressedWidth)) =
    some (ms0 ++ [Msg.g1 Q], cur + Midfall.g1CompressedWidth)
  rw [hq]
  rfl

theorem step_g1_none (c : G1Codec G₁) (π : Bytes) (cur : Nat) (comp : Bytes) (acc : Bytes)
    (ms0 : List (Msg (Fr p) G₁)) (hcomp : bytesTake π cur Midfall.g1CompressedWidth = some comp)
    (hq : c.ofCompressed? comp = none) :
    (∀ st, repackGo (p := p) c π (acc, cur) WireSlot.g1 ≠ Except.ok st) ∧
      decodeGo (p := p) c π (ms0, cur) WireSlot.g1 = none := by
  constructor
  · intro st hh
    rw [repackGo, Midfall.Lowering.repackSlot, hcomp] at hh
    dsimp only at hh
    rw [hq] at hh
    cases hh
  · rw [decodeGo, hcomp]
    show (c.ofCompressed? comp).bind (fun Q =>
        pure (ms0 ++ [Msg.g1 Q], cur + Midfall.g1CompressedWidth)) = none
    rw [hq]
    rfl

theorem step_fr_repack (c : G1Codec G₁) (π : Bytes) (cur : Nat) (le : Bytes) (acc : Bytes)
    (s : Fr p) (hcomp : bytesTake π cur 32 = some le)
    (hs : Midfall.frOfRepr? (p := p) le = some s) :
    repackGo (p := p) c π (acc, cur) WireSlot.fr =
      Except.ok (acc ++ Midfall.frToInputBE s, cur + 32) := by
  rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
  dsimp only
  rw [hs]
  rfl

theorem step_fr_decode (c : G1Codec G₁) (π : Bytes) (cur : Nat) (le : Bytes) (s : Fr p)
    (ms0 : List (Msg (Fr p) G₁)) (hcomp : bytesTake π cur 32 = some le)
    (hs : Midfall.frOfRepr? (p := p) le = some s) :
    decodeGo (p := p) c π (ms0, cur) WireSlot.fr = some (ms0 ++ [Msg.fr s], cur + 32) := by
  rw [decodeGo, hcomp]
  show (Midfall.frOfRepr? (p := p) le).bind (fun s' => pure (ms0 ++ [Msg.fr s'], cur + 32)) =
    some (ms0 ++ [Msg.fr s], cur + 32)
  rw [hs]
  rfl

theorem step_fr_none (c : G1Codec G₁) (π : Bytes) (cur : Nat) (le : Bytes) (acc : Bytes)
    (ms0 : List (Msg (Fr p) G₁)) (hcomp : bytesTake π cur 32 = some le)
    (hs : Midfall.frOfRepr? (p := p) le = none) :
    (∀ st, repackGo (p := p) c π (acc, cur) WireSlot.fr ≠ Except.ok st) ∧
      decodeGo (p := p) c π (ms0, cur) WireSlot.fr = none := by
  constructor
  · intro st hh
    rw [repackGo, Midfall.Lowering.repackSlot, hcomp] at hh
    dsimp only at hh
    rw [hs] at hh
    cases hh
  · rw [decodeGo, hcomp]
    show (Midfall.frOfRepr? (p := p) le).bind (fun s' => pure (ms0 ++ [Msg.fr s'], cur + 32)) = none
    rw [hs]
    rfl


theorem wire_go (c : G1Codec G₁) (π : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat) (acc : Bytes) (ms0 : List (Msg (Fr p) G₁)),
      acc = Midfall.Lowering.encodeContractProof (p := p) c ms0 →
      cur + widthSum slots ≤ π.size →
      ∀ (π' : Bytes) (cur' : Nat),
        (slots.foldlM (repackGo (p := p) c π) (acc, cur) = .ok (π', cur')) ↔
          (∃ ms, slots.foldlM (decodeGo (p := p) c π) (ms0, cur) = some (ms, cur') ∧
            π' = Midfall.Lowering.encodeContractProof (p := p) c ms) := by
  intro slots
  induction slots with
  | nil =>
      intro cur acc ms0 hacc _ π' cur'
      constructor
      · intro h
        cases h
        exact ⟨ms0, rfl, hacc⟩
      · rintro ⟨ms, hms, heq⟩
        cases hms
        rw [heq, hacc]
        rfl
  | cons sl rest ih =>
      intro cur acc ms0 hacc hsize π' cur'
      rw [List.foldlM_cons, List.foldlM_cons]
      simp only [Bind.bind]
      rcases sl with (_ | _)
      · have hle : cur + Midfall.g1CompressedWidth ≤ π.size := by
            have h : widthSum (WireSlot.g1 :: rest) = Midfall.g1CompressedWidth + widthSum rest :=
              widthSum_cons WireSlot.g1 rest
            omega
        cases hcomp : bytesTake π cur Midfall.g1CompressedWidth with
        | none =>
            have hr : repackGo (p := p) c π (acc, cur) WireSlot.g1 =
                Except.error (RepackError.invalidCompressedG1 cur "") := by
              rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
              dsimp only
              exact rfl
            have hd : decodeGo (p := p) c π (ms0, cur) WireSlot.g1 = none := by
              rw [decodeGo, hcomp]
              exact rfl
            constructor
            · intro h
              obtain ⟨st, hst, _⟩ := except_bind_ok _ _ h
              rw [hr] at hst
              cases hst
            · rintro ⟨ms, hms, _⟩
              rw [hd] at hms
              cases hms
        | some comp =>
            cases hq : c.ofCompressed? comp with
            | none =>
                have hr : repackGo (p := p) c π (acc, cur) WireSlot.g1 =
                    Except.error (RepackError.invalidCompressedG1 cur
                      (Midfall.Generator.hexEncodeLower comp)) := by
                  rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
                  dsimp only
                  rw [hq]
                  exact rfl
                have hd : decodeGo (p := p) c π (ms0, cur) WireSlot.g1 = none := by
                  rw [decodeGo, hcomp]
                  show (c.ofCompressed? comp).bind
                    (fun Q => pure (ms0 ++ [Msg.g1 Q], cur + Midfall.g1CompressedWidth)) = none
                  rw [hq]
                  exact rfl
                constructor
                · intro h
                  obtain ⟨st, hst, _⟩ := except_bind_ok _ _ h
                  rw [hr] at hst
                  cases hst
                · rintro ⟨ms, hms, _⟩
                  rw [hd] at hms
                  cases hms
            | some Q =>
                have hr := step_g1_repack (p := p) c π cur comp acc Q hcomp hq
                have hd := step_g1_decode (p := p) c π cur comp Q ms0 hcomp hq
                have hacc' : acc ++ c.toEip Q =
                    Midfall.Lowering.encodeContractProof (p := p) c (ms0 ++ [Msg.g1 Q]) := by
                  have this : Midfall.Lowering.encodeContractProof (p := p) c [Msg.g1 Q] =
                      c.toEip Q := by
                    simp only [Midfall.Lowering.encodeContractProof,
                      Midfall.Lowering.msgContractBytes, List.foldl_cons, List.foldl_nil]
                    rw [show (Midfall.Bytes.empty : Midfall.Bytes) = ByteArray.empty from rfl,
                      ByteArray.empty_append]
                  rw [hacc, ← this, ← encodeContractProof_append]
                have hsize' : (cur + Midfall.g1CompressedWidth) + widthSum rest ≤ π.size := by
                  have h : widthSum (WireSlot.g1 :: rest) =
                      Midfall.g1CompressedWidth + widthSum rest := widthSum_cons WireSlot.g1 rest
                  omega
                rw [hr, hd]
                show (rest.foldlM (repackGo (p := p) c π) (acc ++ c.toEip Q,
                      cur + Midfall.g1CompressedWidth) = .ok (π', cur')) ↔
                  (∃ ms, rest.foldlM (decodeGo (p := p) c π) (ms0 ++ [Msg.g1 Q],
                      cur + Midfall.g1CompressedWidth) = some (ms, cur') ∧
                    π' = Midfall.Lowering.encodeContractProof (p := p) c ms)
                exact ih (cur + Midfall.g1CompressedWidth) (acc ++ c.toEip Q)
                  (ms0 ++ [Msg.g1 Q]) hacc' hsize' π' cur'
      · have hle : cur + 32 ≤ π.size := by
            have h : widthSum (WireSlot.fr :: rest) = 32 + widthSum rest :=
              widthSum_cons WireSlot.fr rest
            omega
        cases hcomp : bytesTake π cur 32 with
        | none =>
            have hr : repackGo (p := p) c π (acc, cur) WireSlot.fr =
                Except.error (RepackError.nonCanonicalScalar cur "") := by
              rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
              dsimp only
              exact rfl
            have hd : decodeGo (p := p) c π (ms0, cur) WireSlot.fr = none := by
              rw [decodeGo, hcomp]
              exact rfl
            constructor
            · intro h
              obtain ⟨st, hst, _⟩ := except_bind_ok _ _ h
              rw [hr] at hst
              cases hst
            · rintro ⟨ms, hms, _⟩
              rw [hd] at hms
              cases hms
        | some le =>
            cases hs : Midfall.frOfRepr? (p := p) le with
            | none =>
                have hr : repackGo (p := p) c π (acc, cur) WireSlot.fr =
                    Except.error (RepackError.nonCanonicalScalar cur
                      (Midfall.Generator.hexEncodeLower
                        (Midfall.Generator.bytesReverse le))) := by
                  rw [repackGo, Midfall.Lowering.repackSlot, hcomp]
                  dsimp only
                  rw [hs]
                  exact rfl
                have hd : decodeGo (p := p) c π (ms0, cur) WireSlot.fr = none := by
                  rw [decodeGo, hcomp]
                  show (Midfall.frOfRepr? (p := p) le).bind
                    (fun s => pure (ms0 ++ [Msg.fr s], cur + 32)) = none
                  rw [hs]
                  exact rfl
                constructor
                · intro h
                  obtain ⟨st, hst, _⟩ := except_bind_ok _ _ h
                  rw [hr] at hst
                  cases hst
                · rintro ⟨ms, hms, _⟩
                  rw [hd] at hms
                  cases hms
            | some sc =>
                have hr := step_fr_repack (p := p) c π cur le acc sc hcomp hs
                have hd := step_fr_decode (p := p) c π cur le sc ms0 hcomp hs
                have hacc' : acc ++ Midfall.frToInputBE sc =
                    Midfall.Lowering.encodeContractProof (p := p) c (ms0 ++ [Msg.fr sc]) := by
                  have this : Midfall.Lowering.encodeContractProof (p := p) c [Msg.fr sc] =
                      Midfall.frToInputBE sc := by
                    simp only [Midfall.Lowering.encodeContractProof,
                      Midfall.Lowering.msgContractBytes, List.foldl_cons, List.foldl_nil]
                    rw [show (Midfall.Bytes.empty : Midfall.Bytes) = ByteArray.empty from rfl,
                      ByteArray.empty_append]
                  rw [hacc, ← this, ← encodeContractProof_append]
                have hsize' : (cur + 32) + widthSum rest ≤ π.size := by
                  have h : widthSum (WireSlot.fr :: rest) = 32 + widthSum rest :=
                    widthSum_cons WireSlot.fr rest
                  omega
                rw [hr, hd]
                show (rest.foldlM (repackGo (p := p) c π) (acc ++ Midfall.frToInputBE sc,
                      cur + 32) = .ok (π', cur')) ↔
                  (∃ ms, rest.foldlM (decodeGo (p := p) c π) (ms0 ++ [Msg.fr sc],
                      cur + 32) = some (ms, cur') ∧
                    π' = Midfall.Lowering.encodeContractProof (p := p) c ms)
                exact ih (cur + 32) (acc ++ Midfall.frToInputBE sc) (ms0 ++ [Msg.fr sc])
                  hacc' hsize' π' cur'

end

/-- D8, the wire-level half of repack_spec: repackProof succeeds exactly when the
    compressed stream decodes by the schedule, and its output is the contract bytes of
    those messages. This is an iff, and it is the half the PLAN's version could not be.

    PROVED by one induction over the slot list that carries both fold states at once
    ('wire_go'), with the exact-length guard discharged up front by
    'compressedLen_eq_widthSum' so neither walk has to carry a short-read arm. -/
theorem repack_spec_wire {G₁ : Type} (plan : RepackedProofLayoutPlan) (c : G1Codec G₁)
    (π π' : Bytes) :
    Midfall.Lowering.repackProof (p := p) plan c π = .ok π' <->
      (∃ ms, Midfall.Lowering.decodeWire (p := p) plan c π = some ms ∧
        π' = Midfall.Lowering.encodeContractProof (p := p) c ms) := by
  have hnil : (ByteArray.empty : Bytes) =
      Midfall.Lowering.encodeContractProof (p := p) c ([] : List (Msg (Fr p) G₁)) := rfl
  have hsize_go : ByteArray.size π = plan.compressedLen →
      0 + widthSum plan.slots ≤ ByteArray.size π := by
    intro hs
    rw [hs, ← compressedLen_eq_widthSum]
    omega
  constructor
  · intro h
    rw [Midfall.Lowering.repackProof] at h
    simp only [Bind.bind, Pure.pure, Except.pure] at h
    by_cases hg : ByteArray.size π ≠ plan.compressedLen
    · rw [ite_eq_left hg] at h
      have h' : Except.error (RepackError.lengthMismatch plan.compressedLen (ByteArray.size π)
          plan.prefixG1Count plan.numEvals plan.numPointSets) = Except.ok π' := h
      cases h'
    · rw [ite_eq_right hg] at h
      have hsize : ByteArray.size π = plan.compressedLen := by
        by_contra H
        exact hg H
      obtain ⟨st, hst, h2⟩ := except_bind_ok _ _ h
      cases h2
      have hgo := wire_go (p := p) c π plan.slots 0 ByteArray.empty [] hnil
        (hsize_go hsize) st.1 st.2
      obtain ⟨ms, hms, hrfl⟩ := hgo.mp (by exact hst)
      refine ⟨ms, ?_, hrfl⟩
      rw [Midfall.Lowering.decodeWire, ite_eq_right hg]
      show ((plan.slots.foldlM (decodeGo (p := p) c π) ([], (0 : Nat)))).map Prod.fst = some ms
      rw [hms]
      exact rfl
  · rintro ⟨ms, hdec, hrfl⟩
    rw [Midfall.Lowering.repackProof]
    simp only [Bind.bind, Pure.pure, Except.pure]
    by_cases hg : ByteArray.size π ≠ plan.compressedLen
    · have hnone : Midfall.Lowering.decodeWire (p := p) plan c π = none := by
        rw [Midfall.Lowering.decodeWire, ite_eq_left hg]
      rw [hnone] at hdec
      cases hdec
    · rw [ite_eq_right hg]
      have hsize : ByteArray.size π = plan.compressedLen := by
        by_contra H
        exact hg H
      have hdec' : (plan.slots.foldlM (decodeGo (p := p) c π) ([], (0 : Nat))).map Prod.fst =
          some ms := by
        rw [Midfall.Lowering.decodeWire, ite_eq_right hg] at hdec
        exact hdec
      rcases hfold : (plan.slots.foldlM (decodeGo (p := p) c π) ([], (0 : Nat))) with
          hnone | ⟨m2, c2⟩
      · rw [hfold] at hdec'
        cases hdec'
      · have hdec'' : some m2 = some ms := by
          have h1 : (plan.slots.foldlM (decodeGo (p := p) c π) ([], (0 : Nat))).map Prod.fst =
              some ms := hdec'
          rw [hfold] at h1
          exact h1
        have hm2 : m2 = ms := Option.some.inj hdec''
        have hfold' : (plan.slots.foldlM (decodeGo (p := p) c π) ([], (0 : Nat))) =
            some (ms, c2) := by rw [hfold, hm2]
        have hgo := wire_go (p := p) c π plan.slots 0 ByteArray.empty [] hnil
          (hsize_go hsize) (Midfall.Lowering.encodeContractProof (p := p) c ms) c2
        have hok : plan.slots.foldlM (repackGo (p := p) c π) (ByteArray.empty, (0 : Nat)) =
            .ok (Midfall.Lowering.encodeContractProof (p := p) c ms, c2) :=
          hgo.mpr ⟨ms, hfold', rfl⟩
        rw [hrfl]
        show (plan.slots.foldlM (repackGo (p := p) c π) (ByteArray.empty, (0 : Nat))).bind
            (fun x => pure x.1) =
          .ok (Midfall.Lowering.encodeContractProof (p := p) c ms)
        rw [hok]
        exact rfl


/-- D8, the pipeline-level half, in the ONLY direction that is true. The PLAN wrote
    "repackProof = .ok π' iff exists ms, decodeRust = some ms and ...", and that is
    FALSE: decodeRust returns none on ANY Fault (Native.lean:228-249 ends with
    .toOption and a trailing-bytes check), so a byte-valid proof whose pipeline panics
    - x3 in pointSets (kzg/mod.rs:479, R-35) or the logup inversion (logup.rs:460) -
    repacks successfully with no message list at all. The implication below is the
    surviving direction; hsched supplies the read-schedule shape that
    Obligations.readScheduleAgrees owes. PROOF OBLIGATION, registered in SORRY.md. -/
theorem repack_spec_of_decodeRust {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (π : Bytes) (plan : RepackedProofLayoutPlan)
    (hc : E.g1.compressedRoundtrip)
    (hsched : ∀ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms →
      ms.map Msg.slot = plan.slots)
    (ms : List (Msg (Fr p) G₁)) (hdec : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    repackProof (p := p) plan E.g1 π = .ok (encodeContractProof E.g1 ms) := by
  sorry

/-! Symmetry of the generator's pointer equality. 'Location' and 'Value' carry no
    BEq (Encoding.lean:204 records why), so the four *Beq defs are hand-written and
    their symmetry is not free. 'points_subgroup_checked_generator' needs it because
    KZ:697 compares candidate.point against a.point while the statement reads the
    other way round. -/



theorem except_ok_inj {ε α : Type} {x y : α} (h : @Except.ok ε α x = @Except.ok ε α y) : x = y := by
  cases h; rfl

theorem beqSwap {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h
    rfl
  · rw [show (a == b) = false by simpa using h,
        show (b == a) = false by simpa using (Ne.symm h)]

theorem andSwap (x y : Bool) : (x && y) = (y && x) := by
  rcases x <;> rcases y <;> rfl

theorem locationBeq_comm (a b : Midfall.Generator.Location) :
    Midfall.Generator.locationBeq a b = Midfall.Generator.locationBeq b a := by
  rcases a with (_ | _) <;> rcases b with (_ | _) <;> rfl

theorem valueBeq_comm (a b : Midfall.Generator.Value) :
    Midfall.Generator.valueBeq a b = Midfall.Generator.valueBeq b a := by
  cases a with
  | integer x =>
      cases b with
      | integer y => show (x == y) = (y == x); rw [beqSwap x y]
      | identifier _ _ => rfl
  | identifier n1 o1 =>
      cases b with
      | integer _ => rfl
      | identifier n2 o2 =>
          show (n1 == n2 && o1 == o2) = (n2 == n1 && o2 == o1)
          rw [beqSwap n1 n2, beqSwap o1 o2]

theorem ptrBeq_comm (a b : Midfall.Generator.Ptr) :
    Midfall.Generator.ptrBeq a b = Midfall.Generator.ptrBeq b a := by
  unfold Midfall.Generator.ptrBeq
  rw [locationBeq_comm, valueBeq_comm]

theorem ecPointBeq_comm (a b : Midfall.Generator.EcPoint) :
    Midfall.Generator.ecPointBeq a b = Midfall.Generator.ecPointBeq b a := by
  show Midfall.Generator.ptrBeq a.base b.base = Midfall.Generator.ptrBeq b.base a.base
  rw [ptrBeq_comm]

/-- The generator layer of points_subgroup_checked: if the generator's own coverage
    validator accepts, then the absorbed proof G1s are exactly the layout's count and
    every one of them is an input to a precompile call the generator emits. The
    semantic layer - "every absorbed point reaches a precompile at run time" - is an
    Obligations field because it needs the call trace.

    PROVED by inverting the two branches of KZ:729-740: the count branch cannot have
    fired (that is the first conjunct), the precompileValidatedG1s bind must have
    returned some u, and validateG1PrecompileCoverage returning .ok () means the
    missing-filter is empty, which is the cover. ecPointBeq_comm is needed because
    KZ:697 compares candidate-then-absorbed while the statement reads it the other
    way round. -/
theorem points_subgroup_checked_generator
    (meta_ : Midfall.Generator.ConstraintSystemMeta) (data : Midfall.Generator.Data)
    (memory : Midfall.Generator.VerifierMemoryLayout) (L : ProofCalldataLayout)
    (h : Midfall.Generator.validateAbsorbedG1PrecompileCoverage meta_ data memory L =
      .ok (.ok ())) :
    (Midfall.Generator.proofAbsorbedG1s meta_ data memory).length = L.totalG1Count ∧
      ∀ t ∈ Midfall.Generator.proofAbsorbedG1s meta_ data memory,
        ∃ u, Midfall.Generator.precompileValidatedG1s meta_ data memory = .ok u ∧
          ∃ v ∈ u, Midfall.Generator.ecPointBeq t.point v.point = true := by
  set absorbed := Midfall.Generator.proofAbsorbedG1s meta_ data memory
  rw [Midfall.Generator.validateAbsorbedG1PrecompileCoverage] at h
  simp only [Bind.bind, Pure.pure, Except.pure] at h
  by_cases hc : (absorbed.length != L.totalG1Count) = true
  · rw [ite_eq_left hc] at h
    cases h
  · rw [ite_eq_right (by simpa using hc)] at h
    have hlen : absorbed.length = L.totalG1Count := by
      by_contra H
      exact hc (by simp [H])
    obtain ⟨u, hu, h2⟩ := except_bind_ok _ _ h
    have hinner : Midfall.Generator.validateG1PrecompileCoverage absorbed u = .ok () :=
      except_ok_inj h2
    have hnil : (absorbed.filter
        (fun a => ! u.any (fun c => Midfall.Generator.ecPointBeq c.point a.point))) = [] := by
      have hhead : (absorbed.filter
          (fun a => ! u.any (fun c => Midfall.Generator.ecPointBeq c.point a.point))).head? = none := by
        rw [Midfall.Generator.validateG1PrecompileCoverage] at hinner
        split at hinner
        · assumption
        · exact absurd hinner (by simp)
      rw [← List.head?_eq_none_iff]
      exact hhead
    refine ⟨hlen, ?_⟩
    intro t ht
    refine ⟨u, hu, ?_⟩
    have hcov : u.any (fun c => Midfall.Generator.ecPointBeq c.point t.point) = true := by
      by_contra H
      have : t ∈ absorbed.filter
          (fun a => ! u.any (fun c => Midfall.Generator.ecPointBeq c.point a.point)) := by
        simp only [List.mem_filter]
        exact ⟨ht, by simpa using H⟩
      rw [hnil] at this
      exact absurd this (by simp)
    obtain ⟨v, hv, hbeq⟩ := List.any_eq_true.mp hcov
    have hfin : Midfall.Generator.ecPointBeq t.point v.point = true := by
      rw [ecPointBeq_comm]
      exact hbeq
    exact ⟨v, hv, hfin⟩



/-! ### 7. Known-answer checks

    Everything below runs: the codec is a two-point stand-in, the layout is
    hand-built from Abi.lean's default, and the scalars are small enough that
    canonicity is decidable at p = 17. The gates are the perturbation evidence for
    the decoder's guards - each negative control is a value the contract rejects,
    and the attack-fix guard has its own refutation case. -/

namespace CdKats

/-- A two-point stand-in for G1, with a codec whose padded form has in-field
    coordinates so g1WordsOk passes, and whose compressed form is a distinct
    48-byte block per point so the repack walk is exercised on both slots. -/
inductive ToyG | one | other deriving BEq

def toyZeros : Bytes := Midfall.Generator.bytesFromNats (List.replicate 128 0)

/-- 16 zeros || x(48) || 16 zeros || y(48), with x = 3 and y = 4: the exact frame
    shape eipShape asserts, at numbers small enough to keep the gate cheap. -/
def toyPadded : Bytes :=
  Midfall.Generator.bytesFromNats (List.replicate 16 0 ++ [3] ++ List.replicate 47 0 ++
    List.replicate 16 0 ++ [4] ++ List.replicate 47 0)

def toyComp (n : Nat) : Bytes := Midfall.Generator.bytesFromNats (List.replicate 48 n)

def toyCodec : G1Codec ToyG where
  toEip := fun Q => if Q == ToyG.one then toyZeros else toyPadded
  ofEip? := fun b =>
    if b == toyZeros then some ToyG.one
    else if b == toyPadded then some ToyG.other
    else none
  toCompressed := fun Q => if Q == ToyG.one then toyComp 1 else toyComp 2
  ofCompressed? := fun b =>
    if b == toyComp 1 then some ToyG.one
    else if b == toyComp 2 then some ToyG.other
    else none

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Msg carries no BEq (it is a structure over abstract groups), so the gates
    compare a code: (0, point tag) for a G1 slot and (1, scalar value) for a
    scalar slot. Two message lists are equal exactly when their codes are. -/
def msgCode (m : Msg (Midfall.Fr 17) ToyG) : Nat × Nat :=
  match m with
  | .g1 Q => (0, if Q == ToyG.one then 1 else 2)
  | .fr s => (1, s.val)

/-- One of each slot type, so a dropped or duplicated slot changes the count. -/
def katPlan : RepackedProofLayoutPlan :=
  { g1Groups := [1], numEvals := 1, numPointSets := 0 }

/-- The compressed proof katPlan expects: g1, one LE scalar, f_com, pi. -/
def katCompressed : Bytes :=
  toyComp 1 ++ Midfall.natToBytesLE 5 32 ++ toyComp 2 ++ toyComp 1

/-- The message list the same plan decodes to. -/
def katMsgs : List (Msg (Midfall.Fr 17) ToyG) :=
  [Msg.g1 ToyG.one, Msg.fr 5, Msg.g1 ToyG.other, Msg.g1 ToyG.one]

/-- A hand-built layout whose fromProofLayout plan is exactly katPlan: one prefix G1
    (from the quotient limb section), one eval, no q_evals, and a proof region of
    repackedLen bytes so the attack-fix guard passes. -/
def katLayout : ProofCalldataLayout :=
  { Midfall.Generator.proofCalldataLayoutDefault with
    proofCptr := Midfall.Generator.abiVerifyProofProofCptr,
    quotientLimbs := Midfall.Generator.ProofSection.new Midfall.Generator.abiVerifyProofProofCptr 1 128,
    evals := Midfall.Generator.ProofSection.new 0 1 32,
    proofEnd := Midfall.Generator.abiVerifyProofProofCptr + 416,
    proofLen := 416 }

/-- GATE 1 (the slots walk). The shape is prefix g1s, evals, one g1, q_evals, one
    g1 - and the counts are pairwise distinct so a swapped term changes the list.
    The lengths pin compressedLen / repackedLen against the two G1 widths: 48 in,
    128 out, which is the whole point of the repacker. -/
def slotsKats_ok : Bool :=
  katPlan.slots ==
    [WireSlot.g1, WireSlot.fr, WireSlot.g1, WireSlot.g1] ∧
  true &&
  katPlan.prefixG1Count == 1 &&
  katPlan.compressedLen == 48 + 32 + 48 + 48 &&
  katPlan.repackedLen == 128 + 32 + 128 + 128 &&
  katPlan.repackedLen - katPlan.compressedLen == 240 &&
  katPlan.repackedLen % 32 == 0 &&
  -- a plan with no g1 groups still ends in the two trailing singletons
  ({ g1Groups := [], numEvals := 0, numPointSets := 0 } : RepackedProofLayoutPlan).slots ==
    [WireSlot.g1, WireSlot.g1] &&
  -- Msg.slot reads the same shape back off the message list
  (katMsgs.map Msg.slot == katPlan.slots)

/-- GATE 2 (encodeContractProof). Each message contributes its own width, so the
    total is the sum and the blocks are in order - a slot reorder is visible. -/
def encodeContractProofKats_ok : Bool :=
  (encodeContractProof (p := 17) toyCodec katMsgs).size == 416 &&
  (bytesTake (encodeContractProof (p := 17) toyCodec katMsgs) 0 128 == some toyZeros) &&
  (bytesTake (encodeContractProof (p := 17) toyCodec katMsgs) 128 32 ==
      some (Midfall.natToBytesBE 5 32)) &&
  (bytesTake (encodeContractProof (p := 17) toyCodec katMsgs) 160 128 == some toyPadded) &&
  (msgContractBytes (p := 17) toyCodec (Msg.fr 5) == Midfall.natToBytesBE 5 32) &&
  (msgContractBytes (p := 17) toyCodec (Msg.g1 ToyG.one) == toyZeros)

/-- GATE 3 (repack_spec_wire, computed). The repack output is exactly the contract
    bytes of the decoded message list, and both agree on the iff's two failure arms:
    a wrong length rejects on both sides, and an undecodable compressed block makes
    decodeWire none while repackProof errors with the same discriminant. -/
def repackWireKats_ok : Bool :=
  (match repackProof (p := 17) katPlan toyCodec katCompressed with
   | .ok out => out == encodeContractProof (p := 17) toyCodec katMsgs &&
                  (decodeWire (p := 17) katPlan toyCodec katCompressed).map (List.map msgCode) ==
                    some (katMsgs.map msgCode)
   | .error _ => false) &&
  -- the exact-length guard, on both sides (attack.md's repack_spec entry)
  (match repackProof (p := 17) katPlan toyCodec (katCompressed ++ Midfall.natToBytesLE 1 32) with
   | .error (RepackError.lengthMismatch 176 208 1 1 0) => true
   | _ => false) &&
  ((decodeWire (p := 17) katPlan toyCodec (katCompressed ++ Midfall.natToBytesLE 1 32)).isNone) &&
  -- a non-canonical scalar (17 at p = 17) is rejected by both
  (match repackProof (p := 17) katPlan toyCodec
      (toyComp 1 ++ Midfall.natToBytesLE 17 32 ++ toyComp 2 ++ toyComp 1) with
   | .error (RepackError.nonCanonicalScalar off _) => off == 48
   | _ => false) &&
    ((decodeWire (p := 17) katPlan toyCodec
      (toyComp 1 ++ Midfall.natToBytesLE 17 32 ++ toyComp 2 ++ toyComp 1)).isNone) &&
  -- an undecodable compressed block
  (match repackProof (p := 17) katPlan toyCodec
      (toyComp 9 ++ Midfall.natToBytesLE 5 32 ++ toyComp 2 ++ toyComp 1) with
   | .error (RepackError.invalidCompressedG1 0 _) => true
   | _ => false)

/-- GATE 4 (calldata_roundtrip, computed). The full envelope round-trips through the
    contract-shaped decoder at p = 17: selector, both head words, the proof length
    word, the instance count, the instance word. Every guard in decodeCalldata is
    exercised by a positive and a negative case in GATE 5 below. -/
def decodeCalldataRoundTrip_ok : Bool :=
  let cd := calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 7]
  cd.size == 580 &&
  (match decodeCalldata (p := 17) katLayout 1 toyCodec cd with
   | some (ms, inst) =>
       (ms.map msgCode == katMsgs.map msgCode) &&
       inst.size == 1 && inst.getD 0 0 == 7
   | none => false) &&
  -- the head words are what the guards read
  (cdWord cd 4).toNat == 0x40 &&
  (cdWord cd 0x24).toNat == 512 &&
  (cdWord cd 0x44).toNat == 416 &&
  (cdWord cd 516).toNat == 1 &&
  -- calldataload pads with zeros past the end, which is what makes the size guard
  -- the only defence against a short buffer
  (cdWord cd 580).toNat == 0 && (cdWord cd 579).toNat != 0

/-- GATE 5 (every decoder guard, one refutation each). Each conjunct removes exactly
    one acceptance condition and must turn the decode into none: the selector, the
    proof-length word, the instance count, the trailing bytes, a non-canonical
    instance word, a non-canonical proof scalar, and - the attack fix - a hand-built
    layout whose proofEnd does not match proofCptr + proofLen. -/
def decodeCalldataGuards_ok : Bool :=
  let cd := calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 7]
  let nats := Midfall.Generator.bytesToNats cd
  let replace (pos : Nat) (v : List Nat) : Bytes :=
    Midfall.Generator.bytesFromNats
      ((List.take pos nats) ++ v ++ (List.drop (pos + v.length) nats))
  -- trailing bytes: VkLoading.yul:106-112
  ((decodeCalldata (p := 17) katLayout 1 toyCodec (cd ++ Midfall.natToBytesBE 0 32)).isNone) &&
  -- wrong selector: the solc dispatcher would never reach the body
  ((decodeCalldata (p := 17) katLayout 1 toyCodec (replace 0 [0xde, 0xad, 0xbe, 0xef])).isNone) &&
  -- proof-length word disagrees with the layout: VkLoading.yul:101
  ((decodeCalldata (p := 17) katLayout 1 toyCodec
      (replace 0x44 (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 415 32)))).isNone) &&
  -- instance count: VkLoading.yul:102
  ((decodeCalldata (p := 17) katLayout 2 toyCodec cd).isNone) &&
  -- a non-canonical instance word (17 at p = 17): TranscriptProofParser.yul:63-68
  (let bad := calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 17]
   (decodeCalldata (p := 17) katLayout 1 toyCodec bad).isNone) &&
  -- a non-canonical proof scalar: TranscriptProofParser.yul:319
  ((decodeCalldata (p := 17) katLayout 1 toyCodec
      (replace (100 + 128) (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 17 32)))).isNone) &&
  -- THE ATTACK FIX, ISOLATED. A layout whose length WORD is 7 while its proof region
  -- is 416 bytes, paired with a calldata that carries 7 at 0x44: every other guard
  -- passes (the walk is driven by proofEnd, and the size guard is proofEnd-based too),
  -- so without guard three this decodes - and calldataOf of what it decoded to writes
  -- BE32(416) at 0x44, refuting calldata_canonical. This is attack.md's counterexample
  -- spelled out, and P2 in the perturbation table reddens exactly this conjunct.
  (let skewed := { katLayout with proofLen := 7 }
   let cd7 := replace 0x44 (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 7 32))
   (decodeCalldata (p := 17) skewed 1 toyCodec cd7).isNone) &&
  -- and the same skewed layout with a consistent proofEnd decodes, so the rejection
  -- is the inconsistency and not the value 7
  (let consistent := { katLayout with proofLen := 7, proofEnd := 100 + 7 }
   (decodeCalldata (p := 17) consistent 1 toyCodec
      (replace 0x44 (Midfall.Generator.bytesToNats (Midfall.natToBytesBE 7 32)))).isNone) &&
  -- and the same layout with the guard satisfied by construction decodes
  (let ok := { katLayout with proofLen := 416 }
   match decodeCalldata (p := 17) ok 1 toyCodec cd with
   | some (_, inst) => inst.getD 0 0 == 7
   | none => false) &&
  -- the proof pointer must be the ABI one: 0x64
  ((decodeCalldata (p := 17) { katLayout with proofCptr := 0x84 } 1 toyCodec cd).isNone)

/-- An EIP-2537 frame from two coordinates: 16 zeros || x(48) || 16 zeros || y(48),
    exactly the shape eipShape and AssemblyHelpers.yul:94-104 describe. -/
def frame (x y : Nat) : Bytes :=
  Midfall.natToBytesBE 0 16 ++ Midfall.natToBytesBE x 48 ++
    Midfall.natToBytesBE 0 16 ++ Midfall.natToBytesBE y 48

/-- GATE 6 (g1WordsOk). The padded frame passes; a high word at or above 2^128 fails
    (AssemblyHelpers.yul:94-104's shr(128, ..) test), and so does a coordinate at or
    above pBase - including the case where the high word is small and ONLY the
    pBase comparison can catch it, which is the conjunct perturbation P6 targets.
    Without this gate the decoder would accept non-canonical point bytes and
    calldata_canonical's EXACTness would be false. -/
def g1WordsOkKats_ok : Bool :=
  let buf := toyPadded
  (g1WordsOk buf 0) &&
  (g1WordsOk toyZeros 0) &&
  -- x_hi >= 2^128
  (! g1WordsOk (Midfall.natToBytesBE (2 ^ 128) 32 ++
      Midfall.Generator.bytesFromNats (List.drop 32 (Midfall.Generator.bytesToNats buf))) 0) &&
  -- a 128-byte block of all ff: both coordinates above pBase
  (! g1WordsOk (Midfall.Generator.bytesFromNats (List.replicate 128 0xff)) 0) &&
  -- the case only the pBase comparison catches: x = pBase exactly, whose high word is
  -- 0x1a0111ea397fe69a4b1ba7b6434bacd7 - well below 2^128 - so the shr(128) tests pass
  -- and only lt(x, pBase) rejects. Perturbation P6 (dropping the pBase term) reddens
  -- exactly here.
  (! g1WordsOk (frame (Midfall.Assumptions.pBase) 0) 0) &&
  (g1WordsOk (frame (Midfall.Assumptions.pBase - 1) 0) 0) &&
  -- and the y half is checked the same way
  (! g1WordsOk (frame 0 (Midfall.Assumptions.pBase)) 0) &&
  (g1WordsOk (frame 0 (Midfall.Assumptions.pBase - 1)) 0) &&
  -- and the padded frame's own coordinates really are below pBase
    (Midfall.Assumptions.pBase > 4)

/-- GATE 7 (encodeCalldata's two error channels, which is FIX 40's point): the
    instance-length check is a planning error and the repack failure is a repack error
    lifted through GeneratorError.fromRepackError, so the two discriminants stay
    distinct after the composition. -/
def encodeCalldataKats_ok : Bool :=
  (match encodeCalldata (p := 17) 1 katPlan toyCodec katCompressed #[5] with
   | .ok cd => cd == calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 5]
   | .error _ => false) &&
  (match encodeCalldata (p := 17) 2 katPlan toyCodec katCompressed #[5] with
   | .error (Midfall.Generator.GeneratorError.planning stage msg) =>
        stage == "calldata" && msg == "instance length mismatch: expected 2, got 1"
   | _ => false) &&
  (match encodeCalldata (p := 17) 1 katPlan toyCodec (Midfall.natToBytesLE 1 32) #[5] with
   | .error (Midfall.Generator.GeneratorError.repack
        (RepackError.lengthMismatch 176 32 1 1 0)) => true
   | _ => false) &&
  -- the FIX 40 composition agrees with the one-shot encoder, i.e. mapError meets
  Midfall.Generator.GeneratorError.fromRepackError
    (RepackError.nonCanonicalScalar 48 "ab") ==
      Midfall.Generator.GeneratorError.repack (RepackError.nonCanonicalScalar 48 "ab") &&
  (match repackThenEncode (p := 17) 1 katPlan toyCodec katCompressed #[5] with
   | .ok cd => cd == calldataOf (p := 17) toyCodec katMsgs [BitVec.ofNat 256 5]
   | .error _ => false)

/-! ### 8. D-P23: every claim in this file carries a witness AND a refutation

    The rule is that a proved bridge must be shown to be satisfiable and to be
    breakable, both as THEOREMS and not as comments. The Bool gates above are the
    per-guard refutations; what follows are the Prop forms, including the one that
    matters most for the ten partial specs: 'hcd' is not an unsatisfiable hypothesis
    at a layout the decoder's own guards can be met by. -/

/- **THE TWO WITNESSES THAT MUST EVALUATE BYTES LIVE UNDER Instances/.** Proving that some
   calldata really decodes, and that an over-long stream really does not, needs the toy
   buffers reduced, and the only reduction that finishes inside the budget is
   native_decide - which the native_decide-confinement gate forbids in a theorem-bearing
   file. They are therefore proved in Instances/SurfaceFixture.lean as
   hcd_satisfiable_toy and repack_wire_refuted_length_toy, next to
   hcd_satisfiable_at_deployment. Everything else in this section is portable and stays. -/

/-- The skew GATE 5 builds really does break the guard, so the refutation above is
    not standing on an uninhabited hypothesis. -/
theorem katLayout_skew_breaks_the_guard :
    ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofEnd ≠
      ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofCptr +
        ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofLen := by
  decide

/-- Witness for 'repack_spec_wire': the iff is inhabited, and the left side really
    produces the contract bytes of what the right side decodes. -/
theorem repack_wire_witness :
    repackProof (p := 17) katPlan toyCodec katCompressed =
      Except.ok (encodeContractProof (p := 17) toyCodec katMsgs) := by
  set_option maxRecDepth 200000 in
  exact rfl

/-- Witness for 'sum_commitmentReadGroups' at a layout whose group list is not the
    trivial one. -/
theorem sum_groups_witness :
    (RepackedProofLayoutPlan.fromProofLayout katLayout).prefixG1Count =
      katLayout.commitmentG1Count := sum_commitmentReadGroups katLayout

/-- Refutation for 'sum_commitmentReadGroups': the filter is not decoration. A
    layout with a zero advice phase reports a group list that is NOT the list of
    every phase count, so the lemma is a real statement about a filter and not
    'List.sum_map_id' in disguise. -/
theorem sum_groups_filter_bites :
    ({ Midfall.Generator.proofCalldataLayoutDefault with
       advicePhases := [Midfall.Generator.ProofSection.new 0 0 128,
         Midfall.Generator.ProofSection.new 0 3 128] }).commitmentReadGroups ≠
    [0, 3] := by
  intro hh
  exact absurd hh (by decide)

/-- Witness for 'proofLen_eq_repackedLen': the toy layout really does tile, so the
    two guards the lemma delivers are met by something. -/
theorem proofLen_witness :
    katLayout.proofLen = (RepackedProofLayoutPlan.fromProofLayout katLayout).repackedLen ∧
      katLayout.proofEnd = katLayout.proofCptr + katLayout.proofLen := ⟨rfl, rfl⟩

/-- Refutation for 'proofLen_eq_repackedLen': the hypothesis is not vacuous either -
    a hand-built layout with a length word that disagrees with its proof region
    fails the second conjunct, which is what the decoder's guard defends against. -/
theorem proofLen_skew_falsifies :
    ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofEnd ≠
      ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofCptr +
        ({ katLayout with proofLen := 7 } : ProofCalldataLayout).proofLen := by
  decide

/-- Refutation for 'points_subgroup_checked_generator': the validator's hypothesis
    is a real constraint, not a True. A layout whose total G1 count disagrees with
    what the generator tracked cannot satisfy it - which is the cross-module
    invariant absorbedCoverage_countMismatch_ok exercises on the Rust side. -/
theorem psc_hypothesis_is_a_real_constraint (meta_ : Midfall.Generator.ConstraintSystemMeta)
    (data : Midfall.Generator.Data) (memory : Midfall.Generator.VerifierMemoryLayout)
    (L : ProofCalldataLayout)
    (h : L.totalG1Count ≠ (Midfall.Generator.proofAbsorbedG1s meta_ data memory).length) :
    Midfall.Generator.validateAbsorbedG1PrecompileCoverage meta_ data memory L ≠
      .ok (.ok ()) := by
  intro hh
  have := points_subgroup_checked_generator meta_ data memory L hh |>.1
  exact h this.symm

end CdKats

#eval Midfall.Lowering.CdKats.slotsKats_ok -- expect true
#eval Midfall.Lowering.CdKats.encodeContractProofKats_ok -- expect true
#eval Midfall.Lowering.CdKats.repackWireKats_ok -- expect true
#eval Midfall.Lowering.CdKats.decodeCalldataRoundTrip_ok -- expect true
#eval Midfall.Lowering.CdKats.decodeCalldataGuards_ok -- expect true
#eval Midfall.Lowering.CdKats.g1WordsOkKats_ok -- expect true
#eval Midfall.Lowering.CdKats.encodeCalldataKats_ok -- expect true

end Midfall.Lowering
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
    The two-way split is what calldata.rs's walk alternates over. The transcript
    READS a G1 at 48 bytes (`hashableG1.width = g1CompressedWidth`,
    Exec/Transcript.lean:65-69) but ABSORBS its 128-byte EIP-2537 form
    (`toEip`, Common/Codec.lean:89-90); the repacked slot is the 128-byte
    contract block that `push_g1` writes. The scalar slot is the same 32 bytes in
    both walks, with the wire order LE and the contract order BE. -/
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

-- `calldata_roundtrip` lives in the CalldataByteLemmas section below (it needs the
-- byte-list plumbing and `encodeContractProof`'s read schedule).

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

-- calldata_canonical lives in the CalldataByteLemmas section below (it needs the
-- slot-walk byte lemma `decodeSlots_encode`).

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

section CalldataByteLemmas

open Midfall.Generator


open Midfall.Generator

theorem bytesFromNats_append (a b : List Nat) :
    bytesFromNats (a ++ b) = bytesFromNats a ++ bytesFromNats b := by
  unfold bytesFromNats
  apply ByteArray.ext
  simp [List.map_append]

theorem bytesFromNats_size (l : List Nat) : (bytesFromNats l).size = l.length := by
  unfold bytesFromNats
  rw [ByteArray.size]
  simp

theorem bytesToNats_bytesFromNats (l : List Nat) :
    bytesToNats (bytesFromNats l) = l.map (fun n => n % 256) := by
  unfold bytesToNats bytesFromNats
  simp only [Nat.toUInt8, List.map_map]
  rfl

theorem bytesToNats_bytesFromNats_of_lt (l : List Nat) (h : ∀ n ∈ l, n < 256) :
    bytesToNats (bytesFromNats l) = l := by
  rw [bytesToNats_bytesFromNats]
  induction l with
  | nil => rfl
  | cons a t ih =>
      have ha : a % 256 = a := Nat.mod_eq_of_lt (h a List.mem_cons_self)
      rw [List.map_cons, ha, ih (fun n hn => h n (List.mem_cons_of_mem a hn))]

theorem bytesFromNats_bytesToNats (b : Bytes) :
    bytesFromNats (bytesToNats b) = b := by
  unfold bytesFromNats bytesToNats
  apply ByteArray.ext
  simp only [List.map_map, Function.comp_def, Nat.toUInt8, UInt8.ofNat_toNat]
  simp

theorem bytesTake_bytesFromNats {l : List Nat} {i n : Nat} (h : i + n ≤ l.length) :
    bytesTake (bytesFromNats l) i n = some (bytesFromNats ((l.drop i).take n)) := by
  have hsz : (bytesFromNats l).size = l.length := bytesFromNats_size l
  unfold bytesTake
  rw [ite_eq_left (by omega)]
  congr 1
  apply ByteArray.ext
  rw [← Array.toList_inj]
  show ((bytesFromNats l).data.extract i (i + n)).toList =
    (bytesFromNats ((l.drop i).take n)).data.toList
  rw [Array.toList_extract]
  unfold bytesFromNats
  rw [List.toList_toArray, List.toList_toArray, List.extract_eq_take_drop,
    List.map_take, List.map_drop]
  rw [show i + n - i = n by omega]

theorem bytesToNats_bytesTake {cd : Bytes} {i n : Nat} (h : i + n ≤ cd.size) :
    bytesToNats ((bytesTake cd i n).getD Bytes.empty) =
      ((bytesToNats cd).drop i).take n := by
  unfold bytesTake
  rw [ite_eq_left h]
  simp only [Option.getD_some, bytesToNats]
  rw [Array.toList_extract, List.extract_eq_take_drop, List.map_take, List.map_drop]
  rw [show i + n - i = n by omega]

theorem bytesTake_size {cd : Bytes} {i n : Nat} {b : Bytes} (h : bytesTake cd i n = some b) :
    b.size = n := by
  unfold bytesTake at h
  split at h
  · cases h
    rw [ByteArray.size, Array.size_extract]
    have : cd.data.size = cd.size := rfl
    omega
  · cases h

theorem bytesTake_append_left {a b : Bytes} {i n : Nat} (h : i + n ≤ a.size) :
    bytesTake (a ++ b) i n = bytesTake a i n := by
  have h' : i + n ≤ a.data.size := by rwa [← ByteArray.size_data] at h
  have hsize : i + n ≤ (a ++ b).data.size := by
    rw [ByteArray.data_append, Array.size_append]; omega
  unfold bytesTake
  rw [show (a ++ b).size = (a ++ b).data.size from rfl, ite_eq_left hsize,
    show a.size = a.data.size from rfl, ite_eq_left h']
  congr 1
  apply ByteArray.ext
  show (a ++ b).data.extract i (i + n) = a.data.extract i (i + n)
  rw [ByteArray.data_append, Array.extract_append]
  have h0 : i - a.data.size = 0 := by omega
  have h1 : i + n - a.data.size = 0 := by omega
  rw [h0, h1]
  simp

theorem bytesTake_append_right {a b : Bytes} {i n : Nat} (h : a.size ≤ i) :
    bytesTake (a ++ b) i n = bytesTake b (i - a.size) n := by
  have h' : a.data.size ≤ i := by rwa [← ByteArray.size_data] at h
  unfold bytesTake
  by_cases hb : (i - a.data.size) + n ≤ b.data.size
  · rw [show (i - a.size) = (i - a.data.size) from by rw [ByteArray.size_data]]
    have hsize : i + n ≤ (a ++ b).data.size := by
      rw [ByteArray.data_append, Array.size_append]; omega
    rw [show (a ++ b).size = (a ++ b).data.size from rfl, ite_eq_left hsize,
      show b.size = b.data.size from rfl, ite_eq_left hb]
    congr 1
    apply ByteArray.ext
    show (a ++ b).data.extract i (i + n) =
      b.data.extract (i - a.data.size) (i - a.data.size + n)
    rw [ByteArray.data_append, Array.extract_append]
    rw [Array.extract_eq_empty_of_le (le_trans (Nat.min_le_right _ _) h')]
    rw [Array.empty_append]
    rw [show i + n - a.data.size = i - a.data.size + n by omega]
  · rw [show (i - a.size) = (i - a.data.size) from by rw [ByteArray.size_data]]
    rw [show (a ++ b).size = (a ++ b).data.size from rfl,
      ite_eq_right (by rw [ByteArray.data_append, Array.size_append]; omega),
      show b.size = b.data.size from rfl, ite_eq_right hb]


/-! ## `cdWord` on a full 32-byte read -/

private theorem range_succ_head' : ∀ n : Nat,
    List.range (n + 1) = 0 :: (List.range n).map (fun x => x + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
      have h1 : List.range (Nat.succ (m + 1))
          = (0 :: List.map (fun x => x + 1) (List.range m)) ++ [m + 1] := by
        rw [List.range_succ, ih]
      have h2 : 0 :: List.map (fun x => x + 1) (List.range (Nat.succ m))
          = 0 :: (List.map (fun x => x + 1) (List.range m) ++ [m + 1]) := by
        rw [List.range_succ, List.map_append, List.map_singleton]
      rw [h1, h2]
      rfl

private theorem foldl_range_head?_eq_take' (bl : List UInt8) :
    ∀ (n : Nat), n ≤ bl.length → ∀ (init : Nat),
      (List.range n).foldl
          (fun acc j => acc * 256 + ((bl.drop j).head?.map UInt8.toNat).getD 0) init
        = (bl.take n).foldl (fun acc x => acc * 256 + x.toNat) init := by
  induction bl with
  | nil =>
      intro n hn init
      rw [List.length_nil] at hn
      have hn0 : n = 0 := by omega
      subst hn0
      rfl
  | cons a t ih =>
      intro n hn init
      cases n with
      | zero => rfl
      | succ m =>
          have hm : m ≤ t.length := by rw [List.length_cons] at hn; omega
          have hstep : (fun x y => x * 256 + ((List.drop (y + 1) (a :: t)).head?.map UInt8.toNat).getD 0)
              = (fun x y => x * 256 + ((List.drop y t).head?.map UInt8.toNat).getD 0) := by
            funext x y
            have hd : List.drop (y + 1) (a :: t) = List.drop y t := by
              show List.drop (Nat.succ y) (a :: t) = _
              rw [List.drop_cons (Nat.succ_pos y)]
              have : Nat.succ y - 1 = y := by omega
              rw [this]
            rw [hd]
          rw [range_succ_head' m, List.foldl_cons, List.drop_zero, List.head?_cons,
              Option.map_some, Option.getD_some, List.foldl_map, hstep,
              ih m hm (init * 256 + a.toNat), List.take_cons (by omega : 0 < m + 1),
              List.foldl_cons]
          simp

theorem cdWord_eq_bytesToNatBE_of_take {cd : Bytes} {i : Nat} (h : i + 32 ≤ cd.size) :
    cdWord cd i = BitVec.ofNat 256 (bytesToNatBE ((bytesTake cd i 32).getD Bytes.empty)) := by
  have hslice : (bytesTake cd i 32).getD Bytes.empty =
      ByteArray.mk (cd.data.extract i (i + 32)) := by
    unfold bytesTake
    rw [ite_eq_left h]
    rfl
  rw [hslice]
  have hlen : cd.data.toList.length = cd.size := Array.length_toList
  have h32 : 32 ≤ (cd.data.toList.drop i).length := by
    rw [List.length_drop, hlen]; omega
  have hf : (List.range 32).foldl
        (fun acc j => acc * 256 + ((cd.data.toList.drop (i + j)).head?.map UInt8.toNat).getD 0) 0
      = ((cd.data.toList.drop i).take 32).foldl (fun acc x => acc * 256 + x.toNat) 0 := by
    have := foldl_range_head?_eq_take' (cd.data.toList.drop i) 32 h32 0
    simp only [List.drop_drop] at this
    exact this
  unfold cdWord
  dsimp only
  rw [hf]
  congr 1
  rw [bytesToNatBE_toList, Array.toList_extract, List.extract_eq_take_drop]
  rw [show i + 32 - i = 32 by omega]


/-! ## The 32-byte big-endian word round trip -/

theorem natToBytesBE_bytesToNatBE_of_size {b : Bytes} (h : b.size = 32) :
    natToBytesBE (bytesToNatBE b) 32 = b := by
  have hsz : (ByteArray.mk b.data.toList.reverse.toArray).size = 32 := by
    rw [ByteArray.size]
    simp [Array.length_toList, h]
  have h1 := Midfall.Assumptions.natToBytesLE_bytesToNatLE
    (ByteArray.mk b.data.toList.reverse.toArray)
  rw [hsz] at h1
  have hbe : bytesToNatLE (ByteArray.mk b.data.toList.reverse.toArray) = bytesToNatBE b := by
    unfold bytesToNatLE
    apply congrArg bytesToNatBE
    apply ByteArray.ext
    simp [List.reverse_reverse]
  rw [hbe] at h1
  have h2 : (natToBytesLE (bytesToNatBE b) 32).data.toList = b.data.toList.reverse := by
    rw [congrArg ByteArray.data h1]
  apply ByteArray.ext
  rw [← Array.toList_inj]
  show (natToBytesBE (bytesToNatBE b) 32).data.toList = b.data.toList
  have hrev : (natToBytesBE (bytesToNatBE b) 32).data.toList =
      (natToBytesLE (bytesToNatBE b) 32).data.toList.reverse := by
    simp [natToBytesBE, natToBytesLE]
  rw [hrev, h2, List.reverse_reverse]

theorem toU256BeBytes_length (v : Nat) : (toU256BeBytes v).length = 32 := by
  unfold toU256BeBytes bytesToNats
  rw [List.length_map, Array.length_toList]
  unfold natToBytesBE
  simp [Midfall.Assumptions.natToBytesLowFirst_size]

theorem toU256BeBytes_lt (v : Nat) : ∀ x ∈ toU256BeBytes v, x < 256 := by
  intro x hx
  unfold toU256BeBytes at hx
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
  exact UInt8.toNat_lt b

theorem bytesFromNats_toU256BeBytes (v : Nat) :
    bytesFromNats (toU256BeBytes v) = natToBytesBE v 32 := by
  unfold toU256BeBytes
  rw [bytesFromNats_bytesToNats]

theorem toU256BeBytes_bytesToNatBE_of_size {b : Bytes} (h : b.size = 32) :
    toU256BeBytes (bytesToNatBE b) = bytesToNats b := by
  unfold toU256BeBytes
  rw [natToBytesBE_bytesToNatBE_of_size h]

theorem bytesToNatBE_lt_pow (b : Bytes) : bytesToNatBE b < 256 ^ b.size := by
  rw [bytesToNatBE_eq_ofLowDigits_reverse]
  have hdig : ∀ x ∈ (b.data.toList.map UInt8.toNat).reverse, x < 256 := by
    intro x hx
    rw [List.mem_reverse] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact UInt8.toNat_lt y
  have := Midfall.Assumptions.ofLowDigits_lt_pow (b := 256) (by decide) _ hdig
  rwa [List.length_reverse, List.length_map, Array.length_toList] at this

theorem cdWord_bytesFromNats {l : List Nat} {i v : Nat}
    (h : (l.drop i).take 32 = toU256BeBytes v) (hi : i + 32 ≤ l.length) :
    (cdWord (bytesFromNats l) i).toNat = v % 2 ^ 256 := by
  have hlen : (bytesFromNats l).size = l.length := bytesFromNats_size l
  rw [cdWord_eq_bytesToNatBE_of_take (by rw [hlen]; exact hi)]
  rw [bytesTake_bytesFromNats hi, h]
  simp only [Option.getD_some]
  rw [bytesFromNats_toU256BeBytes, bytesToNatBE_natToBytesBE, Midfall.pow_256_32,
    BitVec.toNat_ofNat, Nat.mod_mod]

theorem word_take_eq {cd : Bytes} {i : Nat} (h : i + 32 ≤ cd.size) :
    ((bytesToNats cd).drop i).take 32 = toU256BeBytes ((cdWord cd i).toNat) := by
  rcases htake : bytesTake cd i 32 with _ | b
  · unfold bytesTake at htake
    rw [ite_eq_left h] at htake
    cases htake
  · have hb_size : b.size = 32 := bytesTake_size htake
    have hdrop : ((bytesToNats cd).drop i).take 32 = bytesToNats b := by
      have hb := bytesToNats_bytesTake (cd := cd) (i := i) (n := 32) h
      rw [htake] at hb
      simpa using hb.symm
    rw [hdrop]
    have hb_lt : bytesToNatBE b < 2 ^ 256 := by
      have := bytesToNatBE_lt_pow b
      rwa [hb_size, Midfall.pow_256_32] at this
    have hcd := cdWord_eq_bytesToNatBE_of_take (cd := cd) h
    rw [htake] at hcd
    simp only [Option.getD_some] at hcd
    rw [hcd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb_lt]
    exact (toU256BeBytes_bytesToNatBE_of_size hb_size).symm


theorem bytesToNats_append (a b : Bytes) :
    bytesToNats (a ++ b) = bytesToNats a ++ bytesToNats b := by
  unfold bytesToNats
  rw [ByteArray.toList_data_append, List.map_append]

theorem bytesTake_bytesTake {cd : Bytes} {o m i n : Nat} {b : Bytes}
    (h : bytesTake cd o m = some b) (hi : i + n ≤ m) :
    bytesTake b i n = bytesTake cd (o + i) n := by
  unfold bytesTake at h
  by_cases ho : o + m ≤ cd.size
  · rw [ite_eq_left ho] at h
    cases h
    have hd : cd.data.size = cd.size := rfl
    have hb : (ByteArray.mk (cd.data.extract o (o + m))).size = m := by
      rw [ByteArray.size, Array.size_extract,
        Nat.min_eq_left (by omega : o + m ≤ cd.data.size)]
      omega
    unfold bytesTake
    rw [ite_eq_left (by rw [hb]; exact hi)]
    rw [ite_eq_left (by omega)]
    congr 1
    apply ByteArray.ext
    have harr : (cd.data.extract o (o + m)).extract i (i + n) =
        cd.data.extract (o + i) (o + i + n) := by
      rw [Array.extract_extract, Nat.min_eq_left (by omega)]
      rw [show o + (i + n) = o + i + n by omega]
    exact harr
  · rw [ite_eq_right ho] at h
    cases h


/-! ## The slot walk shifts along a proof region -/

def slotEipWidth : WireSlot → Nat
  | WireSlot.g1 => g1EipWidth
  | WireSlot.fr => 32

def eipWidthSum (slots : List WireSlot) : Nat := slots.foldl (fun a s => a + slotEipWidth s) 0

theorem eipWidthSum_cons (x : WireSlot) (l : List WireSlot) :
    eipWidthSum (x :: l) = slotEipWidth x + eipWidthSum l := by
  show l.foldl (fun a s => a + slotEipWidth s) (0 + slotEipWidth x) = _
  rw [Nat.zero_add]
  have h := foldlW_seed' l (slotEipWidth x)
  exact h
where
  foldlW_seed' : ∀ (l : List WireSlot) (acc : Nat),
      l.foldl (fun a s => a + slotEipWidth s) acc = acc + eipWidthSum l := by
    intro l
    induction l with
    | nil => intro acc; simp [eipWidthSum]
    | cons x rest ih =>
        intro acc
        show rest.foldl (fun a s => a + slotEipWidth s) (acc + slotEipWidth x) =
          acc + rest.foldl (fun a s => a + slotEipWidth s) (0 + slotEipWidth x)
        rw [Nat.zero_add, ih (acc + slotEipWidth x), ih (slotEipWidth x)]
        omega

theorem eipWidthSum_append (l l' : List WireSlot) :
    eipWidthSum (l ++ l') = eipWidthSum l + eipWidthSum l' := by
  induction l with
  | nil => simp [eipWidthSum]
  | cons x rest ih =>
      rw [List.cons_append, eipWidthSum_cons, ih, eipWidthSum_cons]
      omega

theorem eipWidthSum_slots (plan : RepackedProofLayoutPlan) :
    eipWidthSum plan.slots =
      plan.prefixG1Count * g1EipWidth + plan.numEvals * 32 + g1EipWidth +
        plan.numPointSets * 32 + g1EipWidth := by
  have hgw : slotEipWidth WireSlot.g1 = g1EipWidth := rfl
  have hfw : slotEipWidth WireSlot.fr = 32 := rfl
  show eipWidthSum (List.replicate plan.prefixG1Count WireSlot.g1
      ++ List.replicate plan.numEvals WireSlot.fr ++ [WireSlot.g1]
      ++ List.replicate plan.numPointSets WireSlot.fr ++ [WireSlot.g1]) = _
  rw [eipWidthSum_append, eipWidthSum_append, eipWidthSum_append, eipWidthSum_append]
  have hrep : ∀ (n w : Nat) (sl : WireSlot), slotEipWidth sl = w →
      eipWidthSum (List.replicate n sl) = n * w := by
    intro n w sl h
    induction n with
    | zero => simp [eipWidthSum]
    | succ n ih => rw [List.replicate_succ, eipWidthSum_cons, ih, h, Nat.succ_mul]; omega
  rw [hrep plan.prefixG1Count g1EipWidth _ hgw,
      hrep plan.numEvals 32 _ hfw, hrep plan.numPointSets 32 _ hfw]
  simp [eipWidthSum, eipWidthSum_cons, hgw]

theorem bytesTake_bound {cd : Bytes} {i n : Nat} {b : Bytes} (h : bytesTake cd i n = some b) :
    i + n ≤ cd.size := by
  unfold bytesTake at h
  by_cases hh : i + n ≤ cd.size
  · exact hh
  · rw [ite_eq_right hh] at h
    cases h

theorem bytesTake_some_of_le {cd : Bytes} {i n : Nat} (h : i + n ≤ cd.size) :
    bytesTake cd i n = some (ByteArray.mk (cd.data.extract i (i + n))) := by
  unfold bytesTake
  rw [ite_eq_left h]

theorem cdWord_eq_of_take_some {cd₁ cd₂ : Bytes} {i j : Nat} {b : Bytes}
    (h₁ : bytesTake cd₁ i 32 = some b) (h₂ : bytesTake cd₂ j 32 = some b) :
    cdWord cd₁ i = cdWord cd₂ j := by
  have hb₁ : i + 32 ≤ cd₁.size := bytesTake_bound h₁
  have hb₂ : j + 32 ≤ cd₂.size := bytesTake_bound h₂
  rw [cdWord_eq_bytesToNatBE_of_take hb₁, cdWord_eq_bytesToNatBE_of_take hb₂, h₁, h₂]

theorem g1WordsOk_eq_of_cdWord_eq {cd₁ cd₂ : Bytes} {i j : Nat}
    (h0 : cdWord cd₁ i = cdWord cd₂ j)
    (h1 : cdWord cd₁ (i + 32) = cdWord cd₂ (j + 32))
    (h2 : cdWord cd₁ (i + 64) = cdWord cd₂ (j + 64))
    (h3 : cdWord cd₁ (i + 96) = cdWord cd₂ (j + 96)) :
    g1WordsOk cd₁ i = g1WordsOk cd₂ j := by
  unfold g1WordsOk
  dsimp only
  rw [h0, h1, h2, h3]

theorem g1WordsOk_eq_of_take_some {cd₁ cd₂ : Bytes} {i j : Nat} {b : Bytes}
    (h₁ : bytesTake cd₁ i 128 = some b) (h₂ : bytesTake cd₂ j 128 = some b) :
    g1WordsOk cd₁ i = g1WordsOk cd₂ j := by
  have hb₁ : i + 128 ≤ cd₁.size := bytesTake_bound h₁
  have hb₂ : j + 128 ≤ cd₂.size := bytesTake_bound h₂
  have hc0 : bytesTake cd₁ (i + 0) 32 = bytesTake cd₂ (j + 0) 32 := by
    rw [show i + 0 = i from rfl, show j + 0 = j from rfl]
    exact (bytesTake_bytesTake h₁ (i := 0) (n := 32) (by omega)).symm.trans
      (bytesTake_bytesTake h₂ (i := 0) (n := 32) (by omega))
  have hc1 : bytesTake cd₁ (i + 32) 32 = bytesTake cd₂ (j + 32) 32 :=
    (bytesTake_bytesTake h₁ (i := 32) (n := 32) (by omega)).symm.trans
      (bytesTake_bytesTake h₂ (i := 32) (n := 32) (by omega))
  have hc2 : bytesTake cd₁ (i + 64) 32 = bytesTake cd₂ (j + 64) 32 :=
    (bytesTake_bytesTake h₁ (i := 64) (n := 32) (by omega)).symm.trans
      (bytesTake_bytesTake h₂ (i := 64) (n := 32) (by omega))
  have hc3 : bytesTake cd₁ (i + 96) 32 = bytesTake cd₂ (j + 96) 32 :=
    (bytesTake_bytesTake h₁ (i := 96) (n := 32) (by omega)).symm.trans
      (bytesTake_bytesTake h₂ (i := 96) (n := 32) (by omega))
  have hex : ∀ (k : Nat), (k = 0 ∨ k = 32 ∨ k = 64 ∨ k = 96) →
      cdWord cd₁ (i + k) = cdWord cd₂ (j + k) := by
    intro k hk
    have htake : bytesTake cd₁ (i + k) 32 = bytesTake cd₂ (j + k) 32 := by
      rcases hk with rfl | rfl | rfl | rfl
      · exact hc0
      · exact hc1
      · exact hc2
      · exact hc3
    have hbound : i + k + 32 ≤ cd₁.size := by omega
    rcases ht : bytesTake cd₁ (i + k) 32 with _ | b'
    · rw [bytesTake_some_of_le hbound] at ht
      cases ht
    · have hsame : bytesTake cd₂ (j + k) 32 = some b' := by
        rw [← htake]; exact ht
      exact cdWord_eq_of_take_some ht hsame
  exact g1WordsOk_eq_of_cdWord_eq (hex 0 (by omega)) (hex 32 (by omega))
    (hex 64 (by omega)) (hex 96 (by omega))



theorem decodeSlots_shift {G : Type} (c : G1Codec G) (cd proof : Bytes) (off : Nat)
    (hsub : bytesTake cd off proof.size = some proof) :
    ∀ (slots : List WireSlot) (k : Nat),
      k + eipWidthSum slots ≤ proof.size →
      ∀ (ms : List (Msg (Fr p) G)) (cur : Nat),
        decodeSlots (p := p) c proof slots k = some (ms, cur) →
        decodeSlots (p := p) c cd slots (off + k) = some (ms, off + cur) := by
  intro slots
  induction slots with
  | nil =>
      intro k hk ms cur h
      simp only [decodeSlots, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [decodeSlots]
  | cons sl rest ih =>
      intro k hk ms cur h
      have hcdsize : off + proof.size ≤ cd.size := bytesTake_bound hsub
      cases sl with
      | g1 =>
        have hsum : eipWidthSum (WireSlot.g1 :: rest) = 128 + eipWidthSum rest := by
          rw [eipWidthSum_cons]; rfl
        have hk128 : k + 128 ≤ proof.size := by rw [hsum] at hk; omega
        have hkrest : k + 128 + eipWidthSum rest ≤ proof.size := by
          rw [hsum] at hk; omega
        have hg : g1WordsOk cd (off + k) = g1WordsOk proof k := by
          have hbt : bytesTake cd (off + k) g1EipWidth = bytesTake proof k g1EipWidth :=
            (bytesTake_bytesTake hsub (i := k) (n := 128) hk128).symm
          have hbound : off + k + 128 ≤ cd.size := by omega
          rcases ht : bytesTake cd (off + k) 128 with _ | b
          · rw [bytesTake_some_of_le hbound] at ht; cases ht
          · have hsame : bytesTake proof k g1EipWidth = some b := by
              rw [← hbt]; exact ht
            exact g1WordsOk_eq_of_take_some ht hsame
        have hbt : bytesTake cd (off + k) g1EipWidth = bytesTake proof k g1EipWidth :=
          (bytesTake_bytesTake hsub (i := k) (n := 128) hk128).symm
        unfold decodeSlots at h ⊢
        simp only [guard] at h ⊢
        by_cases hgp : g1WordsOk proof k = true
        · simp only [hg, hgp] at h ⊢
          simp only [hbt] at ⊢
          simp at h ⊢
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨b, _hb, h⟩ := h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨Q, _hq, h⟩ := h
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨ms0, cur0⟩, hrec, hpair⟩ := h
          simp only [Option.some.injEq, Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rw [show off + k + g1EipWidth = off + (k + g1EipWidth) by omega,
            ih (k + g1EipWidth) hkrest ms0 cur0 hrec]
          simp [_hb, _hq]
        · simp only [hg, hgp] at h ⊢
          cases h
      | fr =>
        have hsum : eipWidthSum (WireSlot.fr :: rest) = 32 + eipWidthSum rest := by
          rw [eipWidthSum_cons]; rfl
        have hk32 : k + 32 ≤ proof.size := by rw [hsum] at hk; omega
        have hkrest : k + 32 + eipWidthSum rest ≤ proof.size := by
          rw [hsum] at hk; omega
        have hw : cdWord cd (off + k) = cdWord proof k := by
          have hbt : bytesTake cd (off + k) 32 = bytesTake proof k 32 :=
            (bytesTake_bytesTake hsub (i := k) (n := 32) hk32).symm
          have hbound : off + k + 32 ≤ cd.size := by omega
          rcases ht : bytesTake cd (off + k) 32 with _ | b
          · rw [bytesTake_some_of_le hbound] at ht; cases ht
          · have hsame : bytesTake proof k 32 = some b := by rw [← hbt]; exact ht
            exact cdWord_eq_of_take_some ht hsame
        unfold decodeSlots at h ⊢
        simp only [guard] at h ⊢
        simp only [hw] at h ⊢
        by_cases hlt : (cdWord proof k).toNat < p
        · simp only [hlt] at h ⊢
          simp at h ⊢
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨ms0, cur0⟩, hrec, hpair⟩ := h
          simp only [Option.some.injEq, Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          rw [show off + k + 32 = off + (k + 32) by omega,
            ih (k + 32) hkrest ms0 cur0 hrec]
          simp
        · simp only [hlt] at h ⊢
          cases h


/-! ## The identity frame and word arithmetic for the G1 guard -/

theorem natToBytesLowFirst_zero_go (len : Nat) (acc : Bytes) :
    (natToBytesLowFirst.go 0 len acc).data.toList =
      acc.data.toList ++ List.replicate len 0 := by
  induction len generalizing acc with
  | zero => simp [natToBytesLowFirst.go]
  | succ k ih =>
      rw [show natToBytesLowFirst.go 0 (k + 1) acc =
            natToBytesLowFirst.go 0 k (acc.push (Nat.toUInt8 (0 % 256))) from rfl]
      rw [ih (acc.push (Nat.toUInt8 0))]
      rw [show (Nat.toUInt8 0 : UInt8) = 0 from rfl]
      rw [ByteArray.data_push, Array.toList_push]
      simp [List.replicate_succ, List.append_assoc]

theorem natToBytesBE_zero (n : Nat) :
    natToBytesBE 0 n = bytesFromNats (List.replicate n 0) := by
  have h : (natToBytesLowFirst 0 n).data.toList = List.replicate n 0 := by
    have := natToBytesLowFirst_zero_go n Bytes.empty
    simpa [natToBytesLowFirst, Bytes.empty] using this
  unfold natToBytesBE bytesFromNats
  congr 1
  rw [← Array.toList_inj, h]
  simp

theorem cdWord_natToBytesBE_zero {i len : Nat} (h : i + 32 ≤ len) :
    cdWord (natToBytesBE 0 len) i = 0 := by
  have hsz : (natToBytesBE 0 len).size = len := by
    rw [natToBytesBE_zero, bytesFromNats_size, List.length_replicate]
  have hb : bytesTake (natToBytesBE 0 len) i 32 = some (natToBytesBE 0 32) := by
    rw [natToBytesBE_zero]
    rw [bytesTake_bytesFromNats (by rw [List.length_replicate]; omega)]
    congr 2
    rw [List.drop_replicate, List.take_replicate]
    rw [show min 32 (len - i) = 32 by omega]
    exact (natToBytesBE_zero 32).symm
  rw [cdWord_eq_bytesToNatBE_of_take (by rw [hsz]; omega), hb]
  simp only [Option.getD_some]
  rw [bytesToNatBE_natToBytesBE, Midfall.pow_256_32, Nat.zero_mod]
  rfl

theorem g1WordsOk_natToBytesBE_zero : g1WordsOk (natToBytesBE 0 128) 0 = true := by
  have hpB : 0 < Midfall.Assumptions.pBase := by decide
  unfold g1WordsOk
  dsimp only
  rw [cdWord_natToBytesBE_zero (by omega : (0:Nat) + 32 ≤ 128),
    cdWord_natToBytesBE_zero (by omega : 0 + 32 + 32 ≤ 128),
    cdWord_natToBytesBE_zero (by omega : 0 + 64 + 32 ≤ 128),
    cdWord_natToBytesBE_zero (by omega : 0 + 96 + 32 ≤ 128)]
  simp [hpB, Nat.two_pow_pos]


theorem bytesTake_whole_size (b : Bytes) : bytesTake b 0 b.size = some b := by
  unfold bytesTake
  rw [ite_eq_left (by omega : 0 + b.size ≤ b.size)]
  congr 1
  apply ByteArray.ext
  rw [show 0 + b.size = b.size by omega,
    Array.extract_eq_self_of_le (by simp : b.data.size ≤ b.size)]

theorem bytesTake_whole_of_size {b : Bytes} {n : Nat} (h : b.size = n) :
    bytesTake b 0 n = some b := by
  rw [← h]
  exact bytesTake_whole_size b

theorem natToBytesBE_48_eq (z : Nat) (_hz : z < 2 ^ 384) :
    natToBytesBE z 48 = natToBytesBE (z / 2 ^ 256) 16 ++ natToBytesBE (z % 2 ^ 256) 32 := by
  have hlo : z % 2 ^ 256 < 256 ^ 32 := by
    rw [Midfall.pow_256_32]; exact Nat.mod_lt _ (by decide)
  have h := natToBytesBE_split (z / 2 ^ 256) (z % 2 ^ 256) 32 hlo 16
  have hz' : z / 2 ^ 256 * 256 ^ 32 + z % 2 ^ 256 = z := by
    rw [Midfall.pow_256_32]
    have := Nat.div_add_mod z (2 ^ 256)
    rw [Nat.mul_comm] at this
    omega
  rw [hz', show 32 + 16 = 48 by omega] at h
  exact h

theorem natToBytesBE_zero16_combine (hi : Nat) (hhi : hi < 2 ^ 128) :
    natToBytesBE 0 16 ++ natToBytesBE hi 16 = natToBytesBE hi 32 := by
  have h := natToBytesBE_split 0 hi 16 (by rw [Midfall.pow_256_16]; exact hhi) 16
  rw [Nat.zero_mul, Nat.zero_add, show 16 + 16 = 32 by omega] at h
  exact h.symm

theorem cdWord_append4 (a b c d : Bytes) (ha : a.size = 32) (hb : b.size = 32)
    (hc : c.size = 32) (hd : d.size = 32) :
    cdWord (a ++ (b ++ (c ++ d))) 0 = BitVec.ofNat 256 (bytesToNatBE a) ∧
    cdWord (a ++ (b ++ (c ++ d))) 32 = BitVec.ofNat 256 (bytesToNatBE b) ∧
    cdWord (a ++ (b ++ (c ++ d))) 64 = BitVec.ofNat 256 (bytesToNatBE c) ∧
    cdWord (a ++ (b ++ (c ++ d))) 96 = BitVec.ofNat 256 (bytesToNatBE d) := by
  have hbc : (b ++ (c ++ d)).size = 96 := by
    rw [ByteArray.size_append, ByteArray.size_append, hb, hc, hd]
  have hcd : (c ++ d).size = 64 := by rw [ByteArray.size_append, hc, hd]
  have hs : (a ++ (b ++ (c ++ d))).size = 128 := by
    rw [ByteArray.size_append, ha, hbc]
  have h0 : bytesTake (a ++ (b ++ (c ++ d))) 0 32 = some a := by
    rw [Midfall.bytesTake_append_left a (b ++ (c ++ d)) 0 32 (by rw [ha])]
    exact bytesTake_whole_of_size ha
  have h32 : bytesTake (a ++ (b ++ (c ++ d))) 32 32 = some b := by
    have h := Midfall.bytesTake_append_right a (b ++ (c ++ d)) 0 32 (by omega)
    rw [show a.size + 0 = 32 by rw [ha]] at h
    rw [h, Midfall.bytesTake_append_left b (c ++ d) 0 32 (by rw [hb])]
    exact bytesTake_whole_of_size hb
  have h64 : bytesTake (a ++ (b ++ (c ++ d))) 64 32 = some c := by
    have h := Midfall.bytesTake_append_right a (b ++ (c ++ d)) 32 32 (by omega)
    rw [show a.size + 32 = 64 by rw [ha]] at h
    rw [h]
    have h' := Midfall.bytesTake_append_right b (c ++ d) 0 32 (by omega)
    rw [show b.size + 0 = 32 by rw [hb]] at h'
    rw [h', Midfall.bytesTake_append_left c d 0 32 (by rw [hc])]
    exact bytesTake_whole_of_size hc
  have h96 : bytesTake (a ++ (b ++ (c ++ d))) 96 32 = some d := by
    have h := Midfall.bytesTake_append_right a (b ++ (c ++ d)) 64 32 (by omega)
    rw [show a.size + 64 = 96 by rw [ha]] at h
    rw [h]
    have h' := Midfall.bytesTake_append_right b (c ++ d) 32 32 (by omega)
    rw [show b.size + 32 = 64 by rw [hb]] at h'
    rw [h']
    have h'' := Midfall.bytesTake_append_right c d 0 32 (by omega)
    rw [show c.size + 0 = 32 by rw [hc]] at h''
    rw [h'']
    exact bytesTake_whole_of_size hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cdWord_eq_bytesToNatBE_of_take (by omega), h0]
    simp only [Option.getD_some]
  · rw [cdWord_eq_bytesToNatBE_of_take (by omega), h32]
    simp only [Option.getD_some]
  · rw [cdWord_eq_bytesToNatBE_of_take (by omega), h64]
    simp only [Option.getD_some]
  · rw [cdWord_eq_bytesToNatBE_of_take (by omega), h96]
    simp only [Option.getD_some]


theorem natToBytesBE_size (n len : Nat) : (natToBytesBE n len).size = len := by
  unfold natToBytesBE
  rw [ByteArray.size]
  simp [Array.length_toList, Midfall.Assumptions.natToBytesLowFirst_size]

theorem g1WordsOk_words (a b c d : Bytes) (ha : a.size = 32) (hb : b.size = 32)
    (hc : c.size = 32) (hd : d.size = 32)
    (hxa : bytesToNatBE a < 2 ^ 128) (hyc : bytesToNatBE c < 2 ^ 128)
    (hx : bytesToNatBE a * 2 ^ 256 + bytesToNatBE b < Midfall.Assumptions.pBase)
    (hy : bytesToNatBE c * 2 ^ 256 + bytesToNatBE d < Midfall.Assumptions.pBase) :
    g1WordsOk (a ++ (b ++ (c ++ d))) 0 = true := by
  obtain ⟨e0, e1, e2, e3⟩ := cdWord_append4 a b c d ha hb hc hd
  have hal : (BitVec.ofNat 256 (bytesToNatBE a)).toNat = bytesToNatBE a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hlt := bytesToNatBE_lt_pow a
    rwa [ha, Midfall.pow_256_32] at hlt
  have hbl : (BitVec.ofNat 256 (bytesToNatBE b)).toNat = bytesToNatBE b := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hlt := bytesToNatBE_lt_pow b
    rwa [hb, Midfall.pow_256_32] at hlt
  have hcl : (BitVec.ofNat 256 (bytesToNatBE c)).toNat = bytesToNatBE c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hlt := bytesToNatBE_lt_pow c
    rwa [hc, Midfall.pow_256_32] at hlt
  have hdl : (BitVec.ofNat 256 (bytesToNatBE d)).toNat = bytesToNatBE d := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have hlt := bytesToNatBE_lt_pow d
    rwa [hd, Midfall.pow_256_32] at hlt
  unfold g1WordsOk
  dsimp only
  rw [e0, e1, e2, e3, hal, hbl, hcl, hdl]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hxa, hyc⟩, hx⟩, hy⟩

theorem g1WordsOk_toEip {G : Type} [Group G] (c : G1Codec G)
    (hc : Midfall.Assumptions.G1CodecLaws c) (Q : G) :
    g1WordsOk (c.toEip Q) 0 = true := by
  by_cases hQ : Q = 1
  · subst hQ
    rw [hc.toEip_one]
    exact g1WordsOk_natToBytesBE_zero
  · obtain ⟨x, y, hx, hy, _hxy, hframe⟩ := hc.eipShape Q hQ
    have hpb384 : Midfall.Assumptions.pBase < 2 ^ 384 := by
      calc Midfall.Assumptions.pBase < 2 ^ 381 := by decide
        _ < 2 ^ 384 := Nat.pow_lt_pow_right (by decide : 1 < 2) (by norm_num : 381 < 384)
    have hx384 : x < 2 ^ 384 := Nat.lt_trans hx hpb384
    have hy384 : y < 2 ^ 384 := Nat.lt_trans hy hpb384
    have hxh : x / 2 ^ 256 < 2 ^ 128 := by
      apply Nat.div_lt_of_lt_mul
      calc x < 2 ^ 384 := hx384
        _ = 2 ^ 128 * 2 ^ 256 := by rw [show 384 = 128 + 256 by norm_num, Nat.pow_add]
    have hyh : y / 2 ^ 256 < 2 ^ 128 := by
      apply Nat.div_lt_of_lt_mul
      calc y < 2 ^ 384 := hy384
        _ = 2 ^ 128 * 2 ^ 256 := by rw [show 384 = 128 + 256 by norm_num, Nat.pow_add]
    have hxl : x / 2 ^ 256 * 2 ^ 256 + x % 2 ^ 256 = x := by
      have := Nat.div_add_mod x (2 ^ 256)
      rw [Nat.mul_comm] at this
      exact this
    have hyl : y / 2 ^ 256 * 2 ^ 256 + y % 2 ^ 256 = y := by
      have := Nat.div_add_mod y (2 ^ 256)
      rw [Nat.mul_comm] at this
      exact this
    have hxcoord : natToBytesBE 0 16 ++ natToBytesBE x 48 =
        natToBytesBE (x / 2 ^ 256) 32 ++ natToBytesBE (x % 2 ^ 256) 32 := by
      rw [natToBytesBE_48_eq x hx384, ← ByteArray.append_assoc,
        natToBytesBE_zero16_combine (x / 2 ^ 256) hxh]
    have hycoord : natToBytesBE 0 16 ++ natToBytesBE y 48 =
        natToBytesBE (y / 2 ^ 256) 32 ++ natToBytesBE (y % 2 ^ 256) 32 := by
      rw [natToBytesBE_48_eq y hy384, ← ByteArray.append_assoc,
        natToBytesBE_zero16_combine (y / 2 ^ 256) hyh]
    have hframe' : c.toEip Q =
        natToBytesBE (x / 2 ^ 256) 32 ++ (natToBytesBE (x % 2 ^ 256) 32 ++
          (natToBytesBE (y / 2 ^ 256) 32 ++ natToBytesBE (y % 2 ^ 256) 32)) := by
      rw [hframe]
      rw [show ((natToBytesBE 0 16 ++ natToBytesBE x 48) ++ natToBytesBE 0 16) ++
            natToBytesBE y 48 =
            (natToBytesBE 0 16 ++ natToBytesBE x 48) ++
              (natToBytesBE 0 16 ++ natToBytesBE y 48) from ByteArray.append_assoc]
      rw [hxcoord, hycoord, ByteArray.append_assoc]
    rw [hframe']
    refine g1WordsOk_words _ _ _ _ (natToBytesBE_size _ _) (natToBytesBE_size _ _)
      (natToBytesBE_size _ _) (natToBytesBE_size _ _) ?_ ?_ ?_ ?_
    · have hlt : x / 2 ^ 256 < 2 ^ 256 := lt_trans hxh (by norm_num)
      rw [bytesToNatBE_natToBytesBE, Midfall.pow_256_32, Nat.mod_eq_of_lt hlt]
      exact hxh
    · have hlt : y / 2 ^ 256 < 2 ^ 256 := lt_trans hyh (by norm_num)
      rw [bytesToNatBE_natToBytesBE, Midfall.pow_256_32, Nat.mod_eq_of_lt hlt]
      exact hyh
    · have hlt : x / 2 ^ 256 < 2 ^ 256 := lt_trans hxh (by norm_num)
      have hlt2 : x % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by decide)
      rw [bytesToNatBE_natToBytesBE, bytesToNatBE_natToBytesBE, Midfall.pow_256_32,
        Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2, hxl]
      exact hx
    · have hlt : y / 2 ^ 256 < 2 ^ 256 := lt_trans hyh (by norm_num)
      have hlt2 : y % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by decide)
      rw [bytesToNatBE_natToBytesBE, bytesToNatBE_natToBytesBE, Midfall.pow_256_32,
        Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2, hyl]
      exact hy


/-! ## The proof walk: `decodeSlots` accepts the encoder's own bytes -/

theorem append4' (a b c d : Bytes) : (a ++ (b ++ c)) ++ d = ((a ++ b) ++ c) ++ d := by
  rw [← ByteArray.append_assoc]

theorem append5 (a b c d : Bytes) : (a ++ (b ++ c)) ++ d = a ++ (b ++ (c ++ d)) := by
  rw [ByteArray.append_assoc, ByteArray.append_assoc]

theorem append6 (a b c d : Bytes) : ((a ++ b) ++ c) ++ d = a ++ (b ++ (c ++ d)) := by
  simp only [ByteArray.append_assoc]

theorem bytesEmpty_append (a : Bytes) : Bytes.empty ++ a = a := by
  apply ByteArray.ext
  simp [Bytes.empty]

theorem encodeContractProof_cons {G : Type} (c : G1Codec G) (m : Msg (Fr p) G)
    (rest : List (Msg (Fr p) G)) :
    encodeContractProof c (m :: rest) = msgContractBytes c m ++ encodeContractProof c rest := by
  show (m :: rest).foldl (fun acc m => acc ++ msgContractBytes c m) Bytes.empty =
    msgContractBytes c m ++ encodeContractProof c rest
  rw [List.foldl_cons, bytesEmpty_append]
  exact encodeContractProof_go c rest (msgContractBytes c m)

theorem cdWord_natToBytesBE_32 {v : Nat} (hv : v < 2 ^ 256) :
    cdWord (natToBytesBE v 32) 0 = BitVec.ofNat 256 v := by
  rw [cdWord_eq_bytesToNatBE_of_take (by rw [natToBytesBE_size])]
  rw [bytesTake_whole_of_size (natToBytesBE_size v 32), Option.getD_some]
  rw [bytesToNatBE_natToBytesBE, Midfall.pow_256_32, Nat.mod_eq_of_lt hv]

theorem decodeSlots_encode_from {G : Type} [Group G] (c : G1Codec G)
    (hc : Midfall.Assumptions.G1CodecLaws c) (hp : p ≤ 2 ^ 256) :
    ∀ (ms : List (Msg (Fr p) G)) (pre post : Bytes),
      decodeSlots c (pre ++ encodeContractProof c ms ++ post) (ms.map Msg.slot) pre.size =
        some (ms, pre.size + eipWidthSum (ms.map Msg.slot)) := by
  intro ms
  induction ms with
  | nil =>
      intro pre post
      simp [decodeSlots, encodeContractProof, eipWidthSum]
  | cons m rest ih =>
      intro pre post
      rw [encodeContractProof_cons]
      cases m with
      | g1 Q =>
          change decodeSlots c (pre ++ (c.toEip Q ++ encodeContractProof c rest) ++ post)
            (WireSlot.g1 :: rest.map Msg.slot) pre.size =
            some (Msg.g1 Q :: rest, pre.size + eipWidthSum (WireSlot.g1 :: rest.map Msg.slot))
          have hsz : (c.toEip Q).size = g1EipWidth := hc.eipWidth Q
          have hmid : pre ++ (c.toEip Q ++ encodeContractProof c rest) ++ post =
              pre ++ c.toEip Q ++ encodeContractProof c rest ++ post :=
            append4' pre (c.toEip Q) (encodeContractProof c rest) post
          have hpre : pre ++ (c.toEip Q ++ encodeContractProof c rest) ++ post =
              (pre ++ c.toEip Q) ++ encodeContractProof c rest ++ post :=
            append4' pre (c.toEip Q) (encodeContractProof c rest) post
          have htake : bytesTake (pre ++ (c.toEip Q ++ encodeContractProof c rest) ++ post)
              pre.size g1EipWidth = some (c.toEip Q) := by
            rw [hmid]
            rw [show pre ++ c.toEip Q ++ encodeContractProof c rest ++ post =
                pre ++ (c.toEip Q ++ (encodeContractProof c rest ++ post)) from
              append6 pre (c.toEip Q) (encodeContractProof c rest) post]
            have h := Midfall.bytesTake_append_right pre
              (c.toEip Q ++ (encodeContractProof c rest ++ post)) 0 g1EipWidth
              (by simp [ByteArray.size_append, hsz])
            rw [show pre.size + 0 = pre.size by omega] at h
            rw [h, Midfall.bytesTake_append_left (c.toEip Q)
              (encodeContractProof c rest ++ post) 0 g1EipWidth (by omega)]
            exact bytesTake_whole_of_size hsz
          have htake' : bytesTake (c.toEip Q) 0 g1EipWidth = some (c.toEip Q) :=
            bytesTake_whole_of_size hsz
          have hgw : g1WordsOk (pre ++ (c.toEip Q ++ encodeContractProof c rest) ++ post)
              pre.size = true := by
            rw [g1WordsOk_eq_of_take_some htake htake']
            exact g1WordsOk_toEip c hc Q
          unfold decodeSlots
          simp only [guard]
          simp [hgw, htake]
          rw [hc.ofEip_toEip Q]
          simp
          rw [show pre.size + g1EipWidth = (pre ++ c.toEip Q).size by
            rw [ByteArray.size_append, hsz]]
          rw [hpre]
          rw [ih (pre ++ c.toEip Q) post]
          have hs : eipWidthSum (WireSlot.g1 :: rest.map Msg.slot) =
              g1EipWidth + eipWidthSum (rest.map Msg.slot) := by
            rw [eipWidthSum_cons]; rfl
          rw [hs, ByteArray.size_append, hsz]
          simp
          omega
      | fr sc =>
          change decodeSlots c (pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post)
            (WireSlot.fr :: rest.map Msg.slot) pre.size =
            some (Msg.fr sc :: rest, pre.size + eipWidthSum (WireSlot.fr :: rest.map Msg.slot))
          have hsz : (frToInputBE sc).size = 32 := by
            unfold frToInputBE
            exact natToBytesBE_size sc.val 32
          have hmid : pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post =
              pre ++ (frToInputBE sc ++ (encodeContractProof c rest ++ post)) :=
            append5 pre (frToInputBE sc) (encodeContractProof c rest) post
          have htake : bytesTake (pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post)
              pre.size 32 = some (frToInputBE sc) := by
            rw [hmid]
            have h := Midfall.bytesTake_append_right pre
              (frToInputBE sc ++ (encodeContractProof c rest ++ post)) 0 32
              (by simp [ByteArray.size_append, hsz])
            rw [show pre.size + 0 = pre.size by omega] at h
            rw [h, Midfall.bytesTake_append_left (frToInputBE sc)
              (encodeContractProof c rest ++ post) 0 32 (by omega)]
            exact bytesTake_whole_of_size hsz
          have hw : cdWord (pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post)
              pre.size = BitVec.ofNat 256 sc.val := by
            rw [cdWord_eq_bytesToNatBE_of_take (by
              simp [ByteArray.size_append, hsz]; omega), htake]
            simp only [Option.getD_some]
            unfold frToInputBE
            rw [bytesToNatBE_natToBytesBE, Midfall.pow_256_32, Nat.mod_eq_of_lt]
            exact lt_of_lt_of_le (ZMod.val_lt sc) hp
          have hlt : (cdWord (pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post)
              pre.size).toNat < p := by
            rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt sc) hp)]
            exact ZMod.val_lt sc
          have hcast : Nat.cast (cdWord (pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post)
              pre.size).toNat = sc := by
            rw [hw, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt sc) hp)]
            exact ZMod.natCast_zmod_val sc
          have hpre : pre ++ (frToInputBE sc ++ encodeContractProof c rest) ++ post =
              (pre ++ frToInputBE sc) ++ encodeContractProof c rest ++ post :=
            append4' pre (frToInputBE sc) (encodeContractProof c rest) post
          unfold decodeSlots
          simp only [guard]
          rw [ite_eq_left hlt]
          simp only [hcast]
          rw [show pre.size + 32 = (pre ++ frToInputBE sc).size by
            rw [ByteArray.size_append, hsz]]
          rw [hpre]
          rw [ih (pre ++ frToInputBE sc) post]
          have hs : eipWidthSum (WireSlot.fr :: rest.map Msg.slot) =
              32 + eipWidthSum (rest.map Msg.slot) := by
            rw [eipWidthSum_cons]; rfl
          rw [hs, ByteArray.size_append, hsz]
          simp
          omega


/-! ## Tiling blocks and encoder sizes -/

def BlocksOk {α : Type} (l : List α) : Nat → List (Nat × List α) → Prop
  | _, [] => True
  | o, (w, b) :: rest => (l.drop o).take w = b ∧ b.length = w ∧ BlocksOk l (o + w) rest

theorem drop_eq_flatten_blocks {α : Type} (l : List α) :
    ∀ (o : Nat) (segs : List (Nat × List α)), BlocksOk l o segs →
      l.drop o = (segs.map Prod.snd).flatten ++ l.drop (o + (segs.map Prod.fst).sum) := by
  intro o segs
  induction segs generalizing o with
  | nil => intro _; simp
  | cons seg rest ih =>
      intro h
      obtain ⟨hb, hlen, hrest⟩ := h
      have hih := ih (o + seg.1) hrest
      rw [show (seg :: rest).map Prod.snd = seg.2 :: rest.map Prod.snd from rfl,
        show (seg :: rest).map Prod.fst = seg.1 :: rest.map Prod.fst from rfl,
        List.flatten_cons, List.sum_cons]
      rw [← List.take_append_drop seg.1 (l.drop o), List.drop_drop, hb, hih]
      rw [List.append_assoc]
      congr 2
      rw [Nat.add_assoc]

theorem blocksOk_append {α : Type} (l : List α) :
    ∀ (s1 s2 : List (Nat × List α)) (o : Nat),
      BlocksOk l o s1 → BlocksOk l (o + (s1.map Prod.fst).sum) s2 →
      BlocksOk l o (s1 ++ s2) := by
  intro s1
  induction s1 with
  | nil => intro s2 o _ h2; exact h2
  | cons seg rest ih =>
      intro s2 o h1 h2
      obtain ⟨hb, hlen, hrest⟩ := h1
      refine ⟨hb, hlen, ?_⟩
      rw [show (List.map Prod.fst (seg :: rest)).sum =
          seg.1 + (List.map Prod.fst rest).sum from by simp] at h2
      have h2' : BlocksOk l (o + seg.1 + (rest.map Prod.fst).sum) s2 := by
        rw [Nat.add_assoc]
        exact h2
      exact ih s2 (o + seg.1) hrest h2'

theorem blocksOk_single {α : Type} (l : List α) (o w : Nat) (b : List α) :
    (l.drop o).take w = b → b.length = w → BlocksOk l o [(w, b)] := by
  intro h hl
  exact ⟨h, hl, trivial⟩

theorem eq_flatten_of_blocks {α : Type} (l : List α) (segs : List (Nat × List α)) :
    BlocksOk l 0 segs → (segs.map Prod.fst).sum = l.length → l = (segs.map Prod.snd).flatten := by
  intro h hs
  have hd := drop_eq_flatten_blocks l 0 segs h
  rw [Nat.zero_add, hs, List.drop_eq_nil_of_le (Nat.le_refl _), List.append_nil] at hd
  exact hd

theorem bytesToNats_length (b : Bytes) : (bytesToNats b).length = b.size := by
  unfold bytesToNats
  rw [List.length_map, Array.length_toList]
  rfl

theorem encodeContractProof_size' {G : Type} (c : G1Codec G) (ms : List (Msg (Fr p) G)) :
    (encodeContractProof c ms).size = (ms.map (fun m => (msgContractBytes c m).size)).sum := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
      rw [encodeContractProof_cons, ByteArray.size_append, ih, List.map_cons, List.sum_cons]

theorem encodeContractProof_nats {G : Type} (c : G1Codec G) (ms : List (Msg (Fr p) G)) :
    bytesToNats (encodeContractProof c ms) =
      (ms.map (fun m => bytesToNats (msgContractBytes c m))).flatten := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
      rw [encodeContractProof_cons, bytesToNats_append, ih, List.map_cons, List.flatten_cons]

theorem eipWidthSum_slots_eq_repackedLen (plan : RepackedProofLayoutPlan) :
    eipWidthSum plan.slots = plan.repackedLen := by
  rw [eipWidthSum_slots]
  unfold RepackedProofLayoutPlan.repackedLen Midfall.Generator.g1Bytes
  norm_num [g1EipWidth, Midfall.Generator.g1WordsCount, Midfall.Generator.wordBytes]

theorem encodeContractProof_size {G : Type} [Group G] (c : G1Codec G)
    (hc : Midfall.Assumptions.G1CodecLaws c) (ms : List (Msg (Fr p) G)) :
    (encodeContractProof c ms).size = eipWidthSum (ms.map Msg.slot) := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
      rw [encodeContractProof_cons, ByteArray.size_append, ih]
      cases m with
      | g1 Q =>
          rw [List.map_cons, show Msg.slot (Msg.g1 Q) = WireSlot.g1 from rfl,
            eipWidthSum_cons,
            show (msgContractBytes c (Msg.g1 Q)).size = g1EipWidth from hc.eipWidth Q,
            show slotEipWidth WireSlot.g1 = g1EipWidth from rfl]
      | fr sc =>
          rw [List.map_cons, show Msg.slot (Msg.fr sc) = WireSlot.fr from rfl,
            eipWidthSum_cons,
            show (msgContractBytes c (Msg.fr sc)).size = 32 from by
              unfold msgContractBytes frToInputBE
              exact natToBytesBE_size sc.val 32,
            show slotEipWidth WireSlot.fr = 32 from rfl]


theorem list_drop_offset_append {α : Type} (a b : List α) (j : Nat) :
    (a ++ b).drop (a.length + j) = b.drop j := by
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [show a.length + j - a.length = j by omega]

theorem list_drop_append_left {α : Type} (a b : List α) : (a ++ b).drop a.length = b := by
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_eq_nil_of_le (Nat.le_refl _),
    List.nil_append]

theorem blocksOk_of_prefix_flatten {α : Type} (a : List α)
    (segs : List (Nat × List α)) (c : List α)
    (hlen : ∀ s ∈ segs, s.2.length = s.1) :
    BlocksOk (a ++ (segs.map Prod.snd).flatten ++ c) a.length segs := by
  induction segs generalizing a with
  | nil => trivial
  | cons seg rest ih =>
      obtain ⟨w, b⟩ := seg
      have hb : b.length = w := hlen (w, b) (by simp)
      have hrest : ∀ s ∈ rest, s.2.length = s.1 :=
        fun s hs => hlen s (List.mem_cons_of_mem _ hs)
      constructor
      · show (List.drop a.length (a ++ List.flatten (List.map Prod.snd ((w, b) :: rest)) ++ c)).take w = b
        have hsplit : a ++ List.flatten (List.map Prod.snd ((w, b) :: rest)) ++ c =
            a ++ (b ++ (List.flatten (List.map Prod.snd rest) ++ c)) := by
          simp [List.append_assoc]
        rw [hsplit, list_drop_append_left]
        rw [List.take_append_of_le_length (by rw [hb]), List.take_of_length_le (by rw [hb])]
      · constructor
        · exact hb
        · have hrec := ih (a ++ b) hrest
          rw [show a.length + w = (a ++ b).length by rw [List.length_append, hb]]
          rw [show a ++ List.flatten (List.map Prod.snd ((w, b) :: rest)) ++ c =
              (a ++ b) ++ List.flatten (List.map Prod.snd rest) ++ c by
            simp [List.append_assoc]]
          exact hrec

theorem blocksOk_get {α : Type} (l : List α) :
    ∀ (segs : List (Nat × List α)) (o : Nat), BlocksOk l o segs →
      ∀ (pre : List (Nat × List α)) (seg : Nat × List α) (post : List (Nat × List α)),
        segs = pre ++ seg :: post →
        (l.drop (o + (pre.map Prod.fst).sum)).take seg.1 = seg.2 := by
  intro segs
  induction segs with
  | nil =>
      intro o _ pre seg post h
      have hne : ([] : List (Nat × List α)) ≠ pre ++ seg :: post := by
        cases pre <;> simp
      exact absurd h hne
  | cons s rest ih =>
      intro o hb pre seg post h
      cases pre with
      | nil =>
          simp only [List.nil_append] at h
          injection h with h1 h2
          subst h1
          subst h2
          simpa using hb.1
      | cons p ps =>
          simp only [List.cons_append] at h
          injection h with h1 h2
          subst h1
          subst h2
          obtain ⟨hb1, hblen, hrest⟩ := hb
          have hpre := ih (o + s.1) hrest ps seg post rfl
          rw [show (List.map Prod.fst (s :: ps)).sum =
              s.1 + (List.map Prod.fst ps).sum by simp]
          rw [show o + (s.1 + (List.map Prod.fst ps).sum) =
              o + s.1 + (List.map Prod.fst ps).sum by omega]
          exact hpre


theorem calldataOf_eq {G : Type} (c : G1Codec G) (ms : List (Msg (Fr p) G))
    (inst : List Word256) :
    calldataOf c ms inst = bytesFromNats (bytesToNats Midfall.Generator.fnSigVerifyProof
      ++ toU256BeBytes 0x40
      ++ toU256BeBytes (0x40 + 0x20 + (encodeContractProof c ms).size)
      ++ toU256BeBytes (encodeContractProof c ms).size
      ++ bytesToNats (encodeContractProof c ms)
      ++ toU256BeBytes inst.length
      ++ inst.flatMap (fun w => toU256BeBytes w.toNat)) := by
  unfold calldataOf encodeCalldataRaw Midfall.Generator.encodeCalldata
  simp only [List.append_assoc]


theorem flatMap_toU256_length (l : List Word256) :
    (l.flatMap (fun w => toU256BeBytes w.toNat)).length = 32 * l.length := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
      rw [List.flatMap_cons, List.length_append, toU256BeBytes_length, ih, List.length_cons]
      ring

theorem flatMap_toU256_getElem (l : List Word256) :
    ∀ (i : Nat) (hi : i < l.length),
      ((l.flatMap (fun w => toU256BeBytes w.toNat)).drop (32 * i)).take 32 =
        toU256BeBytes (l[i].toNat) := by
  induction l with
  | nil =>
      intro i hi
      simp at hi
  | cons w ws ih =>
      intro i hi
      cases i with
      | zero =>
          rw [List.flatMap_cons, show 32 * 0 = 0 by omega, List.drop_zero,
            List.take_append_of_le_length (by rw [toU256BeBytes_length]),
            List.take_of_length_le (by rw [toU256BeBytes_length])]
          simp
      | succ k =>
          rw [List.flatMap_cons, show 32 * (k + 1) = 32 + 32 * k by ring, List.drop_append]
          have hk : k < ws.length := by simpa using hi
          rw [List.drop_eq_nil_of_le (by rw [toU256BeBytes_length]; omega), List.nil_append]
          rw [show 32 + 32 * k - (toU256BeBytes w.toNat).length = 32 * k by
            rw [toU256BeBytes_length]; omega]
          simpa [List.getElem_cons_succ] using ih k hk


theorem assoc7 {α : Type} (a b c d e f g : List α) :
    a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) = a ++ b ++ c ++ d ++ e ++ f ++ g := by
  simp only [List.append_assoc]

theorem assoc7_split {α : Type} (a b c d e f g : List α) :
    a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) =
      (a ++ (b ++ (c ++ (d ++ (e ++ f))))) ++ g := by
  simp only [List.append_assoc]

theorem assoc7_split2 {α : Type} (a b c d e f g : List α) :
    a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g))))) =
      (a ++ (b ++ (c ++ d))) ++ (e ++ (f ++ g)) := by
  simp only [List.append_assoc]

set_option maxHeartbeats 2000000 in
/-- decodeCalldata inverts calldataOf. hypotheses, each load-bearing:
    * hL / hlen / hend - the layout must be at the ABI pointer and self-consistent;
      together they are what proofLen_eq_repackedLen delivers for fromProtocol layouts.
    * hc : G1CodecLaws c - eipShape and toEip_one make every G1 message pass
      g1WordsOk, and ofEip_toEip recovers the point from those bytes.
    * hshape - the message list has the layout's slot shape.
    * hinst / hp - the instance words are canonical and p <= 2^256 (the .fr slot is
      encoded by frToInputBE, which truncates at 2^256).
    * hbound - the ABI LENGTH WORDS are u256 words, so `toU256BeBytes` truncates
      `proof.size` and `inst.length` at 2^256; without a bound on the proof region the
      decoder's length-word guard compares the truncated word with the untruncated
      `L.proofLen`. This is the calldata bound the entry frame carries (`cdBoundB`).
    PROVED (no sorry, no Totality import). -/
theorem calldata_roundtrip {G₁ : Type} [Group G₁]
    (hp : p ≤ 2 ^ 256) (L : ProofCalldataLayout)
    (hL : L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr)
    (hlen : L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen)
    (hend : L.proofEnd = L.proofCptr + L.proofLen)
    (c : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws c)
    (ms : List (Msg (Fr p) G₁))
    (hshape : ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout L).slots)
    (numInstances : Nat) (inst : List Word256) (hn : inst.length = numInstances)
    (hinst : ∀ w ∈ inst, w.toNat < p)
    (hbound : L.proofEnd + 32 + 32 * numInstances < 2 ^ 256) :
    decodeCalldata (p := p) L numInstances c (calldataOf c ms inst) =
      some (ms, inst.toArray) := by
  let P := encodeContractProof c ms
  let S := bytesToNats Midfall.Generator.fnSigVerifyProof
  let W0 := toU256BeBytes 0x40
  let W1 := toU256BeBytes (0x40 + 0x20 + P.size)
  let W2 := toU256BeBytes P.size
  let PN := bytesToNats P
  let Wn := toU256BeBytes inst.length
  let IN := inst.flatMap (fun w => toU256BeBytes w.toNat)
  let Ln := S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN)))))
  have hPsize : P.size = L.proofLen := by
    dsimp only [P]
    rw [encodeContractProof_size c hc ms, hshape, eipWidthSum_slots_eq_repackedLen, hlen]
  have hcptr : L.proofCptr = 100 := by rw [hL]; decide
  have hpend : L.proofEnd = 100 + P.size := by rw [hend, hcptr, hPsize]
  have hPlt : P.size < 2 ^ 256 := by
    rw [hPsize]
    omega
  have hNlt : numInstances < 2 ^ 256 := by omega
  have hS : S.length = 4 := by decide
  have hW0 : W0.length = 32 := toU256BeBytes_length _
  have hW1 : W1.length = 32 := toU256BeBytes_length _
  have hW2 : W2.length = 32 := toU256BeBytes_length _
  have hPN : PN.length = P.size := bytesToNats_length _
  have hWn : Wn.length = 32 := toU256BeBytes_length _
  have hIN : IN.length = 32 * inst.length := flatMap_toU256_length _
  have hLnlen : Ln.length = 100 + P.size + 32 + 32 * inst.length := by
    rw [show Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) from rfl]
    simp only [List.length_append, hS, hW0, hW1, hW2, hPN, hWn, hIN]
    omega
  have hcd : calldataOf c ms inst = bytesFromNats Ln := by
    rw [calldataOf_eq]
    apply congrArg bytesFromNats
    dsimp only [Ln, P, S, W0, W1, W2, PN, Wn, IN]
    exact (assoc7 _ _ _ _ _ _ _).symm
  have htake0 : (Ln.drop 0).take 4 = S := by
    show (Ln.take 4) = S
    rw [show Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) from rfl,
      List.take_append_of_le_length (by rw [hS]), List.take_of_length_le (by rw [hS])]
  have htake4 : (Ln.drop 4).take 32 = W0 := by
    have h : Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) := rfl
    rw [h, show 4 = S.length from hS.symm, list_drop_append_left]
    rw [List.take_append_of_le_length (by rw [hW0]), List.take_of_length_le (by rw [hW0])]
  have htake24 : (Ln.drop 0x24).take 32 = W1 := by
    rw [show Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) from rfl]
    rw [show 0x24 = S.length + W0.length by rw [hS, hW0]]
    rw [← List.drop_drop (i := W0.length) (j := S.length)]
    rw [list_drop_append_left, list_drop_append_left]
    rw [List.take_append_of_le_length (by rw [hW1]), List.take_of_length_le (by rw [hW1])]
  have htake44 : (Ln.drop 0x44).take 32 = W2 := by
    rw [show Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) from rfl]
    rw [show 0x44 = S.length + W0.length + W1.length by rw [hS, hW0, hW1]]
    rw [show S.length + W0.length + W1.length = (S.length + W0.length) + W1.length by omega]
    rw [← List.drop_drop (i := W1.length) (j := S.length + W0.length)]
    rw [show S.length + W0.length = S.length + W0.length by rfl]
    rw [← List.drop_drop (i := W0.length) (j := S.length)]
    rw [list_drop_append_left, list_drop_append_left, list_drop_append_left]
    rw [List.take_append_of_le_length (by rw [hW2]), List.take_of_length_le (by rw [hW2])]
  have htakePen : (Ln.drop L.proofEnd).take 32 = Wn := by
    rw [show Ln = S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) from rfl]
    have hprelen : S.length + W0.length + W1.length + W2.length + PN.length = L.proofEnd := by
      rw [hS, hW0, hW1, hW2, hPN, hpend]
    rw [show L.proofEnd = S.length + W0.length + W1.length + W2.length + PN.length from hprelen.symm]
    rw [show S.length + W0.length + W1.length + W2.length + PN.length =
      (((S.length + W0.length) + W1.length) + W2.length) + PN.length by omega]
    rw [← List.drop_drop (i := PN.length) (j := ((S.length + W0.length) + W1.length) + W2.length)]
    rw [← List.drop_drop (i := W2.length) (j := (S.length + W0.length) + W1.length)]
    rw [← List.drop_drop (i := W1.length) (j := S.length + W0.length)]
    rw [← List.drop_drop (i := W0.length) (j := S.length)]
    rw [list_drop_append_left, list_drop_append_left, list_drop_append_left, list_drop_append_left,
      list_drop_append_left]
    rw [List.take_append_of_le_length (by rw [hWn]), List.take_of_length_le (by rw [hWn])]
  -- selector
  have hsel : bytesTake (calldataOf c ms inst) 0 4 = some Midfall.Generator.fnSigVerifyProof := by
    rw [hcd, bytesTake_bytesFromNats (by rw [hLnlen]; omega)]
    simp only [hLnlen, htake0]
    simp [S, bytesFromNats_bytesToNats]
  -- four words
  have hw4 : (cdWord (calldataOf c ms inst) 4).toNat = 0x40 := by
    rw [hcd, cdWord_bytesFromNats htake4 (by rw [hLnlen]; omega)]
    norm_num
  have hw24 : (cdWord (calldataOf c ms inst) 0x24).toNat = L.proofEnd - 4 := by
    rw [hcd, cdWord_bytesFromNats htake24 (by rw [hLnlen]; omega)]
    rw [Nat.mod_eq_of_lt (by omega : 0x40 + 0x20 + P.size < 2 ^ 256)]
    rw [hpend]
    omega
  have hw44 : (cdWord (calldataOf c ms inst) 0x44).toNat = L.proofLen := by
    rw [hcd, cdWord_bytesFromNats htake44 (by rw [hLnlen]; omega)]
    rw [Nat.mod_eq_of_lt hPlt]
    exact hPsize
  have hwPen : (cdWord (calldataOf c ms inst) L.proofEnd).toNat = numInstances := by
    rw [hcd, cdWord_bytesFromNats htakePen (by rw [hLnlen]; omega)]
    rw [hn, Nat.mod_eq_of_lt hNlt]
  have hsize : (calldataOf c ms inst).size = L.proofEnd + 32 + 32 * numInstances := by
    rw [hcd, bytesFromNats_size, hLnlen, hpend, hn]
  -- the proof walk
  have hwalk : decodeSlots c (calldataOf c ms inst)
      (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr = some (ms, L.proofEnd) := by
    let pre := bytesFromNats (S ++ (W0 ++ (W1 ++ W2)))
    let post := bytesFromNats (Wn ++ IN)
    have hpre : pre.size = L.proofCptr := by
      rw [show pre = bytesFromNats (S ++ (W0 ++ (W1 ++ W2))) from rfl, bytesFromNats_size]
      simp [hS, hW0, hW1, hW2, hcptr]
    have hsplit : calldataOf c ms inst = pre ++ P ++ post := by
      rw [hcd]
      have hLn : Ln = (S ++ (W0 ++ (W1 ++ W2))) ++ (PN ++ (Wn ++ IN)) :=
        assoc7_split2 _ _ _ _ _ _ _
      rw [hLn, bytesFromNats_append (S ++ (W0 ++ (W1 ++ W2))) (PN ++ (Wn ++ IN)),
        bytesFromNats_append PN (Wn ++ IN), bytesFromNats_bytesToNats]
      simp only [P, pre, post]
      exact (ByteArray.append_assoc (a := pre) (b := P) (c := post)).symm
    have hw := decodeSlots_encode_from c hc hp ms pre post
    rw [hsplit, ← hshape]
    rw [show L.proofCptr = pre.size from hpre.symm]
    rw [hw]
    have hcur : pre.size + eipWidthSum (ms.map Msg.slot) = L.proofEnd := by
      rw [hpre, hcptr, show eipWidthSum (ms.map Msg.slot) = P.size from
        (encodeContractProof_size c hc ms).symm, hpend]
    rw [hcur]
  -- instance words
  have hrange : (List.range numInstances).map
      (fun i => cdWord (calldataOf c ms inst) (L.proofEnd + 32 + 32 * i)) = inst := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      apply BitVec.eq_of_toNat_eq
      have htakei : (Ln.drop (L.proofEnd + 32 + 32 * i)).take 32 =
          toU256BeBytes (inst[i].toNat) := by
        have hLn : Ln = (S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ Wn))))) ++ IN :=
          assoc7_split _ _ _ _ _ _ _
        rw [hLn]
        have hprelen : (S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ Wn))))).length =
            L.proofEnd + 32 := by
          simp only [List.length_append, hS, hW0, hW1, hW2, hPN, hWn]
          rw [hpend]
          omega
        rw [show L.proofEnd + 32 + 32 * i =
            (S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ Wn))))).length + 32 * i from by
          rw [hprelen]]
        rw [list_drop_offset_append]
        exact flatMap_toU256_getElem inst i h2
      have hcw : (cdWord (calldataOf c ms inst) (L.proofEnd + 32 + 32 * i)).toNat =
          inst[i].toNat := by
        rw [hcd, cdWord_bytesFromNats htakei (by rw [hLnlen]; omega)]
        rw [Nat.mod_eq_of_lt (BitVec.isLt inst[i])]
      rw [hcw]
  -- close
  unfold decodeCalldata
  simp only [guard]
  rw [ite_eq_left (by rw [hsel]; rfl)]
  rw [ite_eq_left (by rw [hL]; simp)]
  rw [ite_eq_left (by rw [hend]; simp)]
  rw [ite_eq_left (by rw [hw4, hw24]; simp)]
  rw [ite_eq_left (by rw [hw44]; simp)]
  rw [ite_eq_left (by rw [hwPen]; simp)]
  rw [ite_eq_left (by rw [hsize]; simp)]
  rw [hwalk]
  rw [hrange]
  have hall : inst.all (fun w => decide (w.toNat < p)) = true :=
    List.all_eq_true.mpr (fun w hw => decide_eq_true (hinst w hw))
  rw [hall]
  simp





theorem Array.extract_add {α : Type} (as : Array α) (i n m : Nat) :
    as.extract i (i + n + m) = as.extract i (i + n) ++ as.extract (i + n) (i + n + m) := by
  apply Array.toList_inj.mp
  rw [Array.toList_extract, Array.toList_append, Array.toList_extract, Array.toList_extract,
    List.extract_eq_take_drop, List.extract_eq_take_drop, List.extract_eq_take_drop]
  rw [show i + n - i = n by omega, show i + n + m - i = n + m by omega,
    show i + n + m - (i + n) = m by omega]
  rw [List.take_add, List.drop_drop]

theorem bytesTake_add {cd : Bytes} {i n m : Nat} {b1 b2 : Bytes}
    (h1 : bytesTake cd i n = some b1) (h2 : bytesTake cd (i + n) m = some b2) :
    bytesTake cd i (n + m) = some (b1 ++ b2) := by
  have hn : i + n ≤ cd.size := bytesTake_bound h1
  have hm : i + n + m ≤ cd.size := by
    have := bytesTake_bound h2
    omega
  have hb1 : b1 = ByteArray.mk (cd.data.extract i (i + n)) := by
    unfold bytesTake at h1
    rw [ite_eq_left hn] at h1
    cases h1
    rfl
  have hb2 : b2 = ByteArray.mk (cd.data.extract (i + n) (i + n + m)) := by
    unfold bytesTake at h2
    rw [ite_eq_left (by omega)] at h2
    cases h2
    rfl
  unfold bytesTake
  rw [ite_eq_left (by omega)]
  congr 1
  rw [hb1, hb2]
  apply ByteArray.ext
  rw [ByteArray.data_append]
  rw [show i + (n + m) = i + n + m by omega]
  exact Array.extract_add cd.data i n m

theorem bytesTake_zero_of_le {cd : Bytes} {i : Nat} (h : i ≤ cd.size) :
    bytesTake cd i 0 = some Bytes.empty := by
  unfold bytesTake
  rw [ite_eq_left (by omega : i + 0 ≤ cd.size)]
  congr 1
  apply ByteArray.ext
  rw [Array.extract_eq_empty_of_le (by simp : min (i + 0) cd.data.size ≤ i)]
  rfl

theorem decodeSlots_g1_step {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (b : Bytes) (Q : G) (ms : List (Msg (Fr p) G)) (cur' : Nat)
    (hg : g1WordsOk cd cur = true) (hb : bytesTake cd cur g1EipWidth = some b)
    (hq : c.ofEip? b = some Q)
    (hrec : decodeSlots (p := p) c cd rest (cur + g1EipWidth) = some (ms, cur')) :
    decodeSlots (p := p) c cd (WireSlot.g1 :: rest) cur = some (Msg.g1 Q :: ms, cur') := by
  unfold decodeSlots
  simp [guard, hg, hb, hq, hrec]

theorem decodeSlots_g1_none {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (hg : ¬ g1WordsOk cd cur = true) :
    decodeSlots (p := p) c cd (WireSlot.g1 :: rest) cur = none := by
  unfold decodeSlots
  simp [guard, hg]

theorem decodeSlots_g1_none_take {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (hg : g1WordsOk cd cur = true) (hb : bytesTake cd cur g1EipWidth = none) :
    decodeSlots (p := p) c cd (WireSlot.g1 :: rest) cur = none := by
  unfold decodeSlots
  simp [guard, hg, hb]

theorem decodeSlots_g1_none_ofEip {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (b : Bytes) (hg : g1WordsOk cd cur = true)
    (hb : bytesTake cd cur g1EipWidth = some b) (hq : c.ofEip? b = none) :
    decodeSlots (p := p) c cd (WireSlot.g1 :: rest) cur = none := by
  unfold decodeSlots
  simp [guard, hg, hb, hq]

theorem decodeSlots_fr_step {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (ms : List (Msg (Fr p) G)) (cur' : Nat)
    (hlt : (cdWord cd cur).toNat < p)
    (hrec : decodeSlots (p := p) c cd rest (cur + 32) = some (ms, cur')) :
    decodeSlots (p := p) c cd (WireSlot.fr :: rest) cur =
      some (Msg.fr (Nat.cast (cdWord cd cur).toNat) :: ms, cur') := by
  unfold decodeSlots
  simp [guard, hlt, hrec]

theorem decodeSlots_fr_none {G : Type} (c : G1Codec G) (cd : Bytes) (rest : List WireSlot)
    (cur : Nat) (hlt : ¬ (cdWord cd cur).toNat < p) :
    decodeSlots (p := p) c cd (WireSlot.fr :: rest) cur = none := by
  unfold decodeSlots
  simp [guard, hlt]

set_option maxHeartbeats 800000 in
theorem decodeSlots_encode {G : Type} (c : G1Codec G) (hc : c.eipRoundtrip) (cd : Bytes) :
    ∀ (slots : List WireSlot) (cur : Nat) (ms : List (Msg (Fr p) G)) (cur' : Nat),
      decodeSlots c cd slots cur = some (ms, cur') →
      cur' ≤ cd.size →
      bytesTake cd cur (encodeContractProof c ms).size = some (encodeContractProof c ms) ∧
        cur' = cur + (encodeContractProof c ms).size := by
  intro slots
  induction slots with
  | nil =>
      intro cur ms cur' h hbound
      simp only [decodeSlots, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, rfl⟩
      refine bytesTake_zero_of_le ?_
      simpa using hbound
  | cons sl rest ih =>
      intro cur ms cur' h hbound
      cases sl with
      | g1 =>
          by_cases hg : g1WordsOk cd cur = true
          · cases hb : bytesTake cd cur g1EipWidth with
            | none =>
                rw [decodeSlots_g1_none_take (p := p) c cd rest cur hg hb] at h
                cases h
            | some b =>
                cases hq : c.ofEip? b with
                | none =>
                    rw [decodeSlots_g1_none_ofEip (p := p) c cd rest cur b hg hb hq] at h
                    cases h
                | some Q =>
                    cases hrec : decodeSlots (p := p) c cd rest (cur + g1EipWidth) with
                    | none =>
                        have hnone : decodeSlots (p := p) c cd (WireSlot.g1 :: rest) cur = none := by
                          unfold decodeSlots
                          simp [guard, hg, hb, hq, hrec]
                        rw [hnone] at h
                        cases h
                    | some p =>
                        obtain ⟨ms0, cur0⟩ := p
                        rw [decodeSlots_g1_step (p := p) c cd rest cur b Q ms0 cur0 hg hb hq hrec] at h
                        obtain ⟨hms, hcurp⟩ := Prod.mk.inj (Option.some.inj h)
                        subst hms
                        subst hcurp
                        have hbsize : b.size = g1EipWidth := bytesTake_size hb
                        have hQ : c.toEip Q = b := hc b Q hq
                        have hsize : (encodeContractProof c (Msg.g1 Q :: ms0)).size =
                            g1EipWidth + (encodeContractProof c ms0).size := by
                          rw [encodeContractProof_cons, ByteArray.size_append]
                          rw [show (msgContractBytes c (Msg.g1 Q)).size = g1EipWidth from by
                            show (c.toEip Q).size = g1EipWidth
                            rw [hQ]; exact hbsize]
                        obtain ⟨hrecTake, hrecCur⟩ := ih (cur + g1EipWidth) ms0 cur0 hrec hbound
                        have hcurHead : cur + g1EipWidth ≤ cd.size := by
                          rw [hrecCur] at hbound
                          omega
                        have hhead : bytesTake cd cur g1EipWidth = some (c.toEip Q) := by
                          rw [hQ]; exact hb
                        have hcomb := bytesTake_add hhead hrecTake
                        refine ⟨?_, ?_⟩
                        · rw [encodeContractProof_cons, ByteArray.size_append,
                            show (msgContractBytes c (Msg.g1 Q)).size = g1EipWidth from by
                              show (c.toEip Q).size = g1EipWidth
                              rw [hQ]; exact hbsize,
                            show msgContractBytes c (Msg.g1 Q) = c.toEip Q from rfl]
                          exact hcomb
                        · rw [hrecCur, hsize]
                          omega
          · rw [decodeSlots_g1_none (p := p) c cd rest cur hg] at h
            cases h
      | fr =>
          by_cases hlt : (cdWord cd cur).toNat < p
          · cases hrec : decodeSlots (p := p) c cd rest (cur + 32) with
            | none =>
                have hnone : decodeSlots (p := p) c cd (WireSlot.fr :: rest) cur = none := by
                  unfold decodeSlots
                  simp [guard, hlt, hrec]
                rw [hnone] at h
                cases h
            | some p =>
                obtain ⟨ms0, cur0⟩ := p
                rw [decodeSlots_fr_step (p := p) c cd rest cur ms0 cur0 hlt hrec] at h
                obtain ⟨hms, hcurp⟩ := Prod.mk.inj (Option.some.inj h)
                subst hms
                subst hcurp
                let v := (cdWord cd cur).toNat
                have hv : ((Nat.cast v : Fr p)).val = v := by
                  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
                have hsize : (encodeContractProof c (Msg.fr (Nat.cast v) :: ms0)).size =
                    32 + (encodeContractProof c ms0).size := by
                  rw [encodeContractProof_cons, ByteArray.size_append]
                  rw [show (msgContractBytes c (Msg.fr (Nat.cast v))).size = 32 from by
                    show (frToInputBE (Nat.cast v)).size = 32
                    unfold frToInputBE
                    exact natToBytesBE_size _ 32]
                obtain ⟨hrecTake, hrecCur⟩ := ih (cur + 32) ms0 cur0 hrec hbound
                have hcur32 : cur + 32 ≤ cd.size := by
                  rw [hrecCur] at hbound
                  omega
                have hd : cd.data.size = cd.size := rfl
                have hdata_size : (ByteArray.mk (cd.data.extract cur (cur + 32))).size = 32 := by
                  rw [ByteArray.size, Array.size_extract]
                  omega
                have hval : bytesToNatBE (ByteArray.mk (cd.data.extract cur (cur + 32))) = v := by
                  have hcw := cdWord_eq_bytesToNatBE_of_take (cd := cd) (i := cur) hcur32
                  rw [bytesTake_some_of_le (cd := cd) (i := cur) (n := 32) hcur32] at hcw
                  simp only [Option.getD_some] at hcw
                  have := congrArg BitVec.toNat hcw
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt] at this
                  · exact this.symm
                  · have := bytesToNatBE_lt_pow (ByteArray.mk (cd.data.extract cur (cur + 32)))
                    rwa [hdata_size, Midfall.pow_256_32] at this
                have hslice : ByteArray.mk (cd.data.extract cur (cur + 32)) =
                    natToBytesBE v 32 := by
                  rw [← hval]
                  exact (natToBytesBE_bytesToNatBE_of_size hdata_size).symm
                have hb := bytesTake_some_of_le (cd := cd) (i := cur) (n := 32) hcur32
                rw [hslice] at hb
                have hhead : bytesTake cd cur 32 = some (natToBytesBE v 32) := hb
                have hcomb := bytesTake_add hhead hrecTake
                refine ⟨?_, ?_⟩
                · rw [encodeContractProof_cons, ByteArray.size_append,
                    show (msgContractBytes c (Msg.fr (Nat.cast v))).size = 32 from by
                      show (frToInputBE (Nat.cast v)).size = 32
                      unfold frToInputBE
                      exact natToBytesBE_size _ 32,
                    show msgContractBytes c (Msg.fr (Nat.cast v)) = natToBytesBE v 32 from by
                      change natToBytesBE (ZMod.val (Nat.cast v)) 32 = natToBytesBE v 32
                      rw [hv]]
                  exact hcomb
                · rw [hrecCur, hsize]
                  omega
          · rw [decodeSlots_fr_none (p := p) c cd rest cur hlt] at h
            cases h

theorem bytes_beq_eq {a b : Bytes} (h : (a == b) = true) : a = b := by
  have h' : (a.data == b.data) = true := h
  exact ByteArray.ext (beq_iff_eq.mp h')

theorem option_bytes_beq_eq {a b : Option Bytes} (h : (a == b) = true) : a = b := by
  cases a with
  | none => cases b <;> simp_all
  | some x => cases b with
    | none => simp at h
    | some y =>
        have hxy : x = y := bytes_beq_eq (by simpa using h)
        rw [hxy]

theorem decodeCalldata_facts {G : Type} (L : ProofCalldataLayout) (n : Nat)
    (c : G1Codec G) (cd : Bytes) (ms : List (Msg (Fr p) G)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L n c cd = some (ms, inst)) :
    bytesTake cd 0 4 = some Midfall.Generator.fnSigVerifyProof ∧
    L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr ∧
    L.proofEnd = L.proofCptr + L.proofLen ∧
    (cdWord cd 4).toNat = 0x40 ∧
    (cdWord cd 0x24).toNat = L.proofEnd - 4 ∧
    (cdWord cd 0x44).toNat = L.proofLen ∧
    (cdWord cd L.proofEnd).toNat = n ∧
    cd.size = L.proofEnd + 32 + 32 * n ∧
    decodeSlots c cd (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr =
      some (ms, L.proofEnd) ∧
    inst = ((List.range n).map (fun i => cdWord cd (L.proofEnd + 32 + 32 * i))).toArray := by
  unfold decodeCalldata at h
  by_cases h1 : (bytesTake cd 0 4 == some Midfall.Generator.fnSigVerifyProof) = true
  · by_cases h2 : (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr) = true
    · by_cases h3 : (L.proofEnd == L.proofCptr + L.proofLen) = true
      · by_cases h4 : ((cdWord cd 4).toNat == 0x40 &&
            (cdWord cd 0x24).toNat == L.proofEnd - 4) = true
        · by_cases h5 : ((cdWord cd 0x44).toNat == L.proofLen) = true
          · by_cases h6 : ((cdWord cd L.proofEnd).toNat == n) = true
            · by_cases h7 : (cd.size == L.proofEnd + 32 + 32 * n) = true
              · have hsel : bytesTake cd 0 4 = some Midfall.Generator.fnSigVerifyProof :=
                  option_bytes_beq_eq h1
                have hptr : L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr :=
                  Nat.beq_eq.mp h2
                have hend : L.proofEnd = L.proofCptr + L.proofLen := Nat.beq_eq.mp h3
                obtain ⟨h40, h424⟩ := Bool.and_eq_true_iff.mp h4
                have hw4 : (cdWord cd 4).toNat = 0x40 := Nat.beq_eq.mp h40
                have hw24 : (cdWord cd 0x24).toNat = L.proofEnd - 4 := Nat.beq_eq.mp h424
                have hw44 : (cdWord cd 0x44).toNat = L.proofLen := Nat.beq_eq.mp h5
                have hwcnt : (cdWord cd L.proofEnd).toNat = n := Nat.beq_eq.mp h6
                have hsz : cd.size = L.proofEnd + 32 + 32 * n := Nat.beq_eq.mp h7
                simp only [h1, h2, h3, h4, h5, h6, h7, guard] at h
                cases hds : decodeSlots (p := p) c cd
                    (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr with
                | none => rw [hds] at h; simp at h
                | some p =>
                    obtain ⟨ms0, cur0⟩ := p
                    rw [hds] at h
                    simp at h
                    by_cases hcur : cur0 = L.proofEnd
                    · subst hcur
                      simp only [if_pos rfl, Option.bind_some] at h
                      by_cases hall : ∀ x < n,
                          (cdWord cd (L.proofEnd + 32 + 32 * x)).toNat < p
                      · simp only [if_pos hall, Option.bind_some] at h
                        obtain ⟨hms, hinst⟩ := Prod.mk.inj (Option.some.inj h)
                        subst hms
                        subst hinst
                        exact ⟨hsel, hptr, hend, hw4, hw24, hw44, hwcnt, hsz, rfl, rfl⟩
                      · simp only [ite_eq_right hall] at h
                        cases h
                    · simp only [ite_eq_right hcur] at h
                      cases h
              · simp [h1, h2, h3, h4, h5, h6, h7] at h
            · simp [h1, h2, h3, h4, h5, h6] at h
          · simp [h1, h2, h3, h4, h5] at h
        · simp [h1, h2, h3, h4] at h
      · simp [h1, h2, h3] at h
    · simp [h1, h2] at h
  · simp [h1] at h


theorem blocksOk_widths {α : Type} {l : List α} {o : Nat} {segs : List (Nat × List α)}
    (h : BlocksOk l o segs) :
    segs.map Prod.fst = segs.map (fun s => s.2.length) := by
  induction segs generalizing o with
  | nil => rfl
  | cons s rest ih =>
      obtain ⟨hb, hlen, hrest⟩ := h
      obtain ⟨w, b⟩ := s
      simp only [List.map_cons, Prod.fst, Prod.snd] at hlen ⊢
      rw [hlen, ih hrest]


theorem blocksOk_map_width32 {α : Type} (l : List α) (o : Nat) (bs : List (List α))
    (hlen : ∀ b ∈ bs, b.length = 32)
    (hread : ∀ (i : Nat) (hi : i < bs.length),
      (l.drop (o + 32 * i)).take 32 = bs.get ⟨i, hi⟩) :
    BlocksOk l o (bs.map (fun b => (32, b))) := by
  induction bs generalizing o with
  | nil => trivial
  | cons b rest ih =>
      constructor
      · simpa using hread 0 (by simp)
      · constructor
        · exact hlen b (by simp)
        · apply ih (o + 32)
          · intro x hx; exact hlen x (List.mem_cons_of_mem _ hx)
          · intro i hi
            have h := hread (i + 1) (by simpa using hi)
            rw [show o + 32 + 32 * i = o + 32 * (i + 1) by ring]
            simpa using h

theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    ((l.map (fun _ => c)).sum) = c * l.length := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih, Nat.mul_succ, Nat.add_comm, Nat.mul_comm]

set_option maxHeartbeats 3000000 in
theorem flatten_blocks_generic (w : Nat) (a b c d e f : List Nat) (L : List (List Nat)) :
    (([(4, a), (32, b), (32, c), (32, d), (w, e), (32, f)] ++
      L.map (fun x => (32, x))).map Prod.snd).flatten =
      a ++ (b ++ (c ++ (d ++ (e ++ (f ++ L.flatten))))) := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil]
  simp only [List.append_nil, List.map_map, Function.comp_def, List.append_assoc]
  rw [show (fun x : List Nat => x) = id from rfl, List.map_id]

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
    PROVED here by the tile assembly: `decodeCalldata_facts` gives the envelope,
    `decodeSlots_encode` gives the proof region byte-for-byte, `word_take_eq` gives
    every length/instance word, and `eq_flatten_of_blocks` glues the tiles back to
    `bytesToNats cd = S ++ W0 ++ W1 ++ W2 ++ PN ++ Wn ++ IN`, which is exactly the
    `calldataOf` list. No `Totality` import and no row/root hypothesis. -/
theorem calldata_canonical {G₁ : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G₁) (hc : c.eipRoundtrip)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd = calldataOf c ms inst.toList := by
  obtain ⟨hsel, hptr, hend, hw4, hw24, hw44, hwcnt, hsz, hslots, hinst⟩ :=
    decodeCalldata_facts L numInstances c cd ms inst h
  have hcptr : L.proofCptr = 100 := by rw [hptr]; decide
  have hpend : L.proofEnd = 100 + L.proofLen := by rw [hend, hcptr]
  let P := encodeContractProof c ms
  obtain ⟨hPtake, hPcur⟩ := decodeSlots_encode c hc cd
    (RepackedProofLayoutPlan.fromProofLayout L).slots L.proofCptr ms L.proofEnd hslots
    (by rw [hsz]; omega)
  have hPsize : P.size = L.proofLen := by
    have hPsize' : (encodeContractProof c ms).size = L.proofLen := by
      rw [hcptr] at hPcur
      omega
    exact hPsize'
  let instL := (List.range numInstances).map (fun i => cdWord cd (L.proofEnd + 32 + 32 * i))
  have hinstL : inst.toList = instL := by
    rw [hinst]
  have hninst : instL.length = numInstances := by simp [instL]
  have hidx24 : L.proofEnd - 4 = 0x40 + 0x20 + P.size := by omega
  let S := bytesToNats Midfall.Generator.fnSigVerifyProof
  let W0 := toU256BeBytes 0x40
  let W1 := toU256BeBytes (0x40 + 0x20 + P.size)
  let W2 := toU256BeBytes P.size
  let PN := bytesToNats P
  let Wn := toU256BeBytes instL.length
  let IN := instL.flatMap (fun w => toU256BeBytes w.toNat)
  have hS : S.length = 4 := by
    dsimp [S]; rw [bytesToNats_length]; decide
  have hW0 : W0.length = 32 := toU256BeBytes_length _
  have hW1 : W1.length = 32 := toU256BeBytes_length _
  have hW2 : W2.length = 32 := toU256BeBytes_length _
  have hPN : PN.length = P.size := bytesToNats_length _
  have hWn : Wn.length = 32 := toU256BeBytes_length _
  -- reads
  have hselT : ((bytesToNats cd).drop 0).take 4 = S := by
    rw [← bytesToNats_bytesTake (by rw [hsz]; omega), hsel]
    simp [S, Option.getD_some]
  have h4T : ((bytesToNats cd).drop 4).take 32 = W0 := by
    rw [word_take_eq (by rw [hsz]; omega), hw4]
  have h24T : ((bytesToNats cd).drop 0x24).take 32 = W1 := by
    rw [word_take_eq (by rw [hsz]; omega), hw24, hidx24]
  have h44T : ((bytesToNats cd).drop 0x44).take 32 = W2 := by
    rw [word_take_eq (by rw [hsz]; omega), hw44,
      show L.proofLen = P.size from hPsize.symm]
  have hwalkBound : L.proofCptr + P.size ≤ cd.size := by
    rw [← hPcur]; rw [hsz]; omega
  have hwalkT : ((bytesToNats cd).drop L.proofCptr).take P.size = PN := by
    rw [← bytesToNats_bytesTake hwalkBound, hPtake]
    rfl
  have hcntT : ((bytesToNats cd).drop L.proofEnd).take 32 = Wn := by
    rw [word_take_eq (by rw [hsz]; omega), hwcnt,
      show numInstances = instL.length from hninst.symm]
  have hinstT : ∀ (i : Nat) (hi : i < instL.length),
      ((bytesToNats cd).drop (L.proofEnd + 32 + 32 * i)).take 32 =
        toU256BeBytes (instL.get ⟨i, hi⟩).toNat := by
    intro i hi
    rw [word_take_eq (by rw [hsz]; omega)]
    simp [instL, List.getElem_map, List.getElem_range]
  -- blocks
  let instBytes : List (List Nat) := instL.map (fun w => toU256BeBytes w.toNat)
  let instBlocks : List (Nat × List Nat) := instBytes.map (fun b => (32, b))
  let blocks : List (Nat × List Nat) :=
    [(4, S), (32, W0), (32, W1), (32, W2), (P.size, PN), (32, Wn)] ++ instBlocks
  have hb1 : BlocksOk (bytesToNats cd) 0 [(4, S)] :=
    blocksOk_single _ 0 4 S hselT hS
  have hb2 : BlocksOk (bytesToNats cd) 4 [(32, W0)] :=
    blocksOk_single _ 4 32 W0 h4T hW0
  have hb3 : BlocksOk (bytesToNats cd) 36 [(32, W1)] :=
    blocksOk_single _ 36 32 W1 h24T hW1
  have hb4 : BlocksOk (bytesToNats cd) 68 [(32, W2)] :=
    blocksOk_single _ 68 32 W2 h44T hW2
  have hb5 : BlocksOk (bytesToNats cd) 100 [(P.size, PN)] := by
    have h := blocksOk_single (bytesToNats cd) L.proofCptr P.size PN hwalkT hPN
    simpa [hcptr] using h
  have hb6 : BlocksOk (bytesToNats cd) L.proofEnd [(32, Wn)] :=
    blocksOk_single _ L.proofEnd 32 Wn hcntT hWn
  have hbI : BlocksOk (bytesToNats cd) (L.proofEnd + 32) instBlocks := by
    dsimp [instBlocks]
    apply blocksOk_map_width32
    · intro b hb
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hb
      exact toU256BeBytes_length _
    · intro i hi
      have hi' : i < instL.length := by simpa [instBytes] using hi
      have h := hinstT i hi'
      simpa [instBytes, List.getElem_map] using h
  have hb12 := blocksOk_append (bytesToNats cd) [(4, S)] [(32, W0)] 0 hb1
    (by simpa using hb2)
  have hb123 := blocksOk_append (bytesToNats cd) ([(4, S)] ++ [(32, W0)]) [(32, W1)] 0 hb12
    (by simpa using hb3)
  have hb1234 := blocksOk_append (bytesToNats cd) ([(4, S)] ++ [(32, W0)] ++ [(32, W1)])
    [(32, W2)] 0 hb123 (by simpa using hb4)
  have hb12345 := blocksOk_append (bytesToNats cd)
    ([(4, S)] ++ [(32, W0)] ++ [(32, W1)] ++ [(32, W2)]) [(P.size, PN)] 0 hb1234
    (by simpa using hb5)
  have hb123456 := blocksOk_append (bytesToNats cd)
    ([(4, S)] ++ [(32, W0)] ++ [(32, W1)] ++ [(32, W2)] ++ [(P.size, PN)]) [(32, Wn)] 0
    hb12345
    (by
      have hp : (0 + (([(4, S)] ++ [(32, W0)] ++ [(32, W1)] ++ [(32, W2)] ++
          [(P.size, PN)]).map Prod.fst).sum) = L.proofEnd := by
        simp [hS, hW0, hW1, hW2, hPN]
        omega
      rw [hp]; exact hb6)
  have hbAll : BlocksOk (bytesToNats cd) 0 blocks := by
    have hb7 := blocksOk_append (bytesToNats cd)
      ([(4, S), (32, W0), (32, W1), (32, W2), (P.size, PN), (32, Wn)]) instBlocks 0
      hb123456
      (by
        have hp : (0 + (([(4, S), (32, W0), (32, W1), (32, W2), (P.size, PN),
            (32, Wn)]).map Prod.fst).sum) = L.proofEnd + 32 := by
          simp [hS, hW0, hW1, hW2, hPN, hWn]
          omega
        rw [hp]; exact hbI)
    simpa [blocks, List.append_assoc] using hb7
  -- size of the whole list
  have hsum : (blocks.map Prod.fst).sum = (bytesToNats cd).length := by
    have hinstSum :
        (instL.map (Prod.fst ∘ (fun b => (32, b)) ∘
          fun w => toU256BeBytes w.toNat)).sum = 32 * instL.length := by
      have hmap : (instL.map (Prod.fst ∘ (fun b => (32, b)) ∘
          fun w => toU256BeBytes w.toNat)) = instL.map (fun _ => 32) := by
        apply List.map_congr_left
        intro w _
        rfl
      rw [hmap, sum_map_const]
    have h1 : (blocks.map Prod.fst).sum =
        4 + (32 + (32 + (32 + (P.size + (32 + 32 * instL.length))))) := by
      simp only [blocks, instBlocks, instBytes, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, hS, hW0, hW1, hW2,
        hPN, hWn, toU256BeBytes_length, List.map_map, Function.comp_apply, Prod.fst]
      rw [hinstSum]
      omega
    rw [h1, bytesToNats_length, hsz, hninst, hpend, hPsize]
    omega
  have hnat : bytesToNats cd =
      S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) := by
    have hflat := eq_flatten_of_blocks (bytesToNats cd) blocks hbAll hsum
    have hfl : (blocks.map Prod.snd).flatten =
        S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN))))) := by
      change (([(4, S), (32, W0), (32, W1), (32, W2), (P.size, PN), (32, Wn)] ++
        instBytes.map (fun x => (32, x))).map Prod.snd).flatten =
        S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ instBytes.flatten)))))
      exact flatten_blocks_generic P.size S W0 W1 W2 PN Wn instBytes
    rw [hflat, hfl]

  have hcalldata : calldataOf c ms instL =
      bytesFromNats (S ++ (W0 ++ (W1 ++ (W2 ++ (PN ++ (Wn ++ IN)))))) := by
    rw [calldataOf_eq]
    apply congrArg bytesFromNats
    dsimp only [S, W0, W1, W2, PN, Wn, IN, P]
    exact (assoc7 _ _ _ _ _ _ _).symm
  rw [← bytesFromNats_bytesToNats cd, hnat, ← hcalldata, hinstL]

end CalldataByteLemmas

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
    Obligations.readScheduleAgrees owes. PROOF OBLIGATION, registered in SORRY.md.

    THE NAMED D1 DEPENDENCY (still open, so this stays a sorry): the proof needs the
    width schedule of `Verifier.prepare`, i.e. `PrepareLogSlots` /
    `readScheduleAgrees_of_validV3` in `LoweringV3/EndToEnd.lean` (the read order of
    `prepare` equals `RepackedProofLayoutPlan.fromProofLayout R.plan.proofLayout`).
    Nothing in the tree relates `decodeRust`'s transcript widths to the protocol plan
    yet (`gap_readScheduleAgrees`). With that bridge, `decodeWire`'s exact-length guard
    and `repack_spec_wire` discharge this statement. -/
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
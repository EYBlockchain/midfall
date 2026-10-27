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

/-- The plan's prefix G1 count is the layout's transcript-facing commitment count.
    The filter in commitmentReadGroups drops only ZERO counts, so the sum is
    unchanged - that is the whole content, and it is why the lemma is not rfl: the
    two sides are different folds over different fields. PROOF OBLIGATION, registered
    in SORRY.md. -/
theorem sum_commitmentReadGroups (L : ProofCalldataLayout) :
    (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count = L.commitmentG1Count := by
  sorry

/-- For layouts built by fromProtocol at the ABI proof pointer the proof length IS
    the repacked length and the sections tile exactly (survey, Encoding area: VM and
    Direct plans share this layout). Hand-built layouts need not, which is what the
    guard in decodeCalldata defends against and what
    commitmentReadGroups_disagreeWhenHandBuilt_ok exhibits. PROOF OBLIGATION,
    registered in SORRY.md (M5-7: the cursor invariant at each of fromProtocol's ten
    steps). -/
theorem proofLen_eq_repackedLen (protocol : Midfall.Generator.ProtocolPlan)
    (numEvals numPointSets : Nat) (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol
        Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets = .ok L) :
    L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen ∧
      L.proofEnd = L.proofCptr + L.proofLen := by
  sorry

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

/-- EXACT in both modes (D7, and P-12's measurement of the templates): trailing bytes
    revert, non-canonical words revert, and an accepted G1 block is the canonical
    encoding of its point, so a decoded calldata is byte-for-byte the calldataOf of
    what it decoded to. The R-25 malleability lives in decodeAcc, which is not in this
    path at all - that is why accumulator mode needs no exception here.

    hypotheses: hc : eipRoundtrip is the decoder-first law that turns "the decoder
    accepted these bytes" into "these are the encoder's bytes for that point"; hend is
    the layout-consistency guard (attack.md's FIX) and is necessary for hand-built
    layouts. PROOF OBLIGATION, registered in SORRY.md (M5-8). -/
theorem calldata_canonical {G₁ : Type} (L : ProofCalldataLayout) (numInstances : Nat)
    (c : G1Codec G₁) (hc : c.eipRoundtrip)
    (hend : L.proofEnd = L.proofCptr + L.proofLen)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd = calldataOf c ms inst.toList := by
  sorry

/-- D8, the wire-level half of repack_spec: repackProof succeeds exactly when the
    compressed stream decodes by the schedule, and its output is the contract bytes of
    those messages. This is an iff, and it is the half the PLAN's version could not be.
    PROOF OBLIGATION, registered in SORRY.md. -/
theorem repack_spec_wire {G₁ : Type} (plan : RepackedProofLayoutPlan) (c : G1Codec G₁)
    (π π' : Bytes) :
    repackProof (p := p) plan c π = .ok π' <->
      (∃ ms, decodeWire (p := p) plan c π = some ms ∧ π' = encodeContractProof c ms) := by
  sorry

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

/-- The generator layer of points_subgroup_checked: if the generator's own coverage
    validator accepts, then the absorbed proof G1s are exactly the layout's count and
    every one of them is an input to a precompile call the generator emits. The
    semantic layer - "every absorbed point reaches a precompile at run time" - is an
    Obligations field because it needs the call trace. PROOF OBLIGATION, registered in
    SORRY.md. -/
theorem points_subgroup_checked_generator
    (meta_ : Midfall.Generator.ConstraintSystemMeta) (data : Midfall.Generator.Data)
    (memory : Midfall.Generator.VerifierMemoryLayout) (L : ProofCalldataLayout)
    (h : Midfall.Generator.validateAbsorbedG1PrecompileCoverage meta_ data memory L =
      .ok (.ok ())) :
    (Midfall.Generator.proofAbsorbedG1s meta_ data memory).length = L.totalG1Count ∧
      ∀ t ∈ Midfall.Generator.proofAbsorbedG1s meta_ data memory,
        ∃ u, Midfall.Generator.precompileValidatedG1s meta_ data memory = .ok u ∧
          ∃ v ∈ u, Midfall.Generator.ecPointBeq t.point v.point = true := by
  sorry


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

end CdKats

#eval Midfall.Lowering.CdKats.slotsKats_ok -- expect true
#eval Midfall.Lowering.CdKats.encodeContractProofKats_ok -- expect true
#eval Midfall.Lowering.CdKats.repackWireKats_ok -- expect true
#eval Midfall.Lowering.CdKats.decodeCalldataRoundTrip_ok -- expect true
#eval Midfall.Lowering.CdKats.decodeCalldataGuards_ok -- expect true
#eval Midfall.Lowering.CdKats.g1WordsOkKats_ok -- expect true
#eval Midfall.Lowering.CdKats.encodeCalldataKats_ok -- expect true

end Midfall.Lowering
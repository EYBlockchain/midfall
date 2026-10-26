# DESIGN 1: Codecs, accumulator, calldata and the quotient VM: every statement typed over the Exec/Generator objects that exist today, with the unported pieces (LoweringPlan, SolidityGenerator, validator, Yul emitter, accFixedBases producer) abstracted as Surface fields or Obligations-structure fields, and everything statable over existing types written as a plain theorem with a registered proof hole.

## files
### formal/Midfall/Assumptions/Codec.lean
G1CodecLaws: the named codec hypothesis structure (decoder-first eip/compressed round trips from Codec.lean:106/113, plus the encoder-first law, the EIP byte shape with in-field non-(0,0) coordinates, identity = 128 zero bytes, compressed width 48). Consumed by decodeAcc_encode, decodeAcc_injective, calldata_roundtrip/canonical and the provable restatement of verifyNative_iff_msgs.
imports: Midfall.Common.Codec, Midfall.Common.Bytes, Midfall.Assumptions.Pairing
hazards:
- R-34: no Lean instance proves any law; every law stays a binder
- Instances/Bls12_381.lean g1AffineCodec must NOT be imported (D-P17)
- needs [Group G₁] only for (1 : G₁); do not add [DecidableEq] binders (D-P7)
### formal/Midfall/Lowering/AccEncoding.lean
D-P16 reconciliation: toExecKind/toExec and lemmas (a)-(d) between Midfall.Generator.AccumulatorEncoding and the Exec stand-in, with the n < 2^64-1 bound and its counterexample gate.
imports: Midfall.Generator.Api, Midfall.Halo2.Exec.Accumulator
hazards:
- AccumulatorEncoding / AccumulatorEncodingKind are ambiguous with both namespaces open: always fully qualify
- Generator fullyCollapsedPublicInputWords/validateForNumInstances/fixedScalarCount sit in a mutual block (Api.lean:562-633): unfold with their equation lemmas
- ApiFault/GeneratorError derive BEq only: state ok-ness via Except.isOk / Except.toOption, never `= .ok ()` under decide
### formal/Midfall/Lowering/Accumulator.lean
accWords (R-25 projection), decodeAcc_injective, negateByTable + decodeAcc_encode (collapsed .pointAndScalar), S5 batched_complete / batched_atMostOneRoot, decideBool/MSMKZG.eval algebra, dualMsm_check_iff_contract (check-level pairing lift), ContractRefAcceptsAcc with the accumulator arm, contractRef_acc_complete.
imports: Midfall.Lowering.AccEncoding, Midfall.Assumptions.Codec, Midfall.Halo2.Exec.Accumulator, Midfall.Halo2.Exec.Native, Midfall.Lowering.Types, Midfall.Halo2.Spec.Lemmas
hazards:
- decodeAcc/KzgAcc have phantom G₂ Gₜ and implicit p: write (p := p) (G₂ := G₂) (Gₜ := Gₜ) at every call
- Midfall.Halo2.fixedBases inserts "-G" ↦ (1:G₁)⁻¹ = identity (Accumulator.lean:502, defect): never route a statement through it; pass tbl := fb.map (name, base)
- decodeAcc's `-s` on a Nat at Accumulator.lean:987 has never been compiled; run #check @Midfall.Halo2.decodeAcc first
- sorry tokens must sit in one digit band (checks.sh:13-19 sort mismatch) and the s-word must not appear in doc comments (lean_grep.py apostrophe hazard)
### formal/Midfall/Lowering/VkDigest.lean
feToU256_frToRepr: the deployed VK_DIGEST word equals frWord vk.transcriptRepr, stated over Encoding.feToU256 ∘ bytesToNats ∘ frToRepr so it does NOT import Generator.Vk (which pulls Midfall.Instances.ExponentModel transitively, D-P17 hazard). The generateBaseVk corollary is an Obligations field, not a theorem.
imports: Midfall.Generator.Encoding, Midfall.Halo2.Exec.Accumulator, Midfall.Common.Codec
hazards:
- Generator.Word (pointer newtype, Encoding.lean:289) vs Midfall.Word256: do not `open Midfall.Generator` unqualified
- Encoding.lean imports Midfall.Yul.Externals: Midfall.Yul.modexpFrameBytes vs Midfall.Generator.modexpFrameBytes clash if both opened
### formal/Midfall/Lowering/Calldata.lean
Theorem-side calldata codec over ProofCalldataLayout + G1Codec, typed over raw Bytes/Word256: WireSlot, RepackedProofLayoutPlan.slots, encodeContractProof, repackProof (port of calldata.rs:43-128), encodeCalldataRaw/encodeCalldata (evm.rs:22-38 + calldata.rs:132-149), calldataOf, decodeWire, decodeCalldata (the contract's acceptance checks), lemmas repackedLen_mod32 / proofLen_eq_repackedLen, theorems repack_spec (split), calldata_roundtrip, calldata_canonical.
imports: Midfall.Generator.Abi, Midfall.Generator.Quotient.VmTypes, Midfall.Generator.Encoding, Midfall.Halo2.Exec.Native, Midfall.Halo2.Exec.Accumulator, Midfall.Assumptions.Codec
hazards:
- two GeneratorError types: use Midfall.Generator.GeneratorError (Api.lean:309), never Midfall.Lowering.GeneratorError
- ByteArray equality: use BEq (==) in Bool guards, DecidableEq ByteArray is not relied on elsewhere in the tree
- the contract's `lt(word, r)` is the literal FR_MODULUS; decodeCalldata checks `< p` and the Surface pins p = Midfall.Assumptions.r
- PLAN's repack_spec iff is FALSE (byte-valid proof whose pipeline panics); file states the split form
### formal/Midfall/Lowering/Qvm.lean
QVMFr ↔ Fr r bridge (qvmFrModulus_eq_r, qvmToFr homomorphism lemmas), Valuation, evalExprρ (token domain wraps mod 256), memOfρ / NoMiss / CacheConsistent (∀ρ via a pre-populated cache, no VmReference change), shape denotations + RecognizersSound + noShapeRecognizers_sound, exprBounded, buildItems/buildPlan (local plan-items driver), qvm_compile_correct_identity (form b), qvm_compile_correct_certifier / _program (form a), builder_segments_total (noOOB builder form).
imports: Midfall.Generator.Quotient.VmReference, Midfall.Generator.Quotient.VmBuilder, Midfall.Generator.Quotient.VmCertify, Midfall.Assumptions.Pairing
hazards:
- do NOT `open Midfall.Generator.QVM`: QVM.Fr (abbrev Nat) shadows Midfall.Fr
- QuotientExpr/QuotientMem/QuotientTarget/QVMFault derive BEq only: state with `=`, prove `==`→`=` by cases
- fuel-local names unfold as evalQuotientIdentityLoop.go / identitySegment.go / segmentMaxStackGo
- emitU32 truncates and pushByte pushes raw Nats (VmBuilder.lean:348): hypotheses go through exprBounded or post-finish bytes
- Yul PUSH_CONST is a raw mload while fqFromU256 panics at ≥ r: every QVM statement carries `∀ c ∈ consts, c.toNat < qvmFrModulus`
### formal/Midfall/Lowering/QvmFold.lean
The whole-stream fold as a NEW definition: expandItem/globalIdentities (inline ++ expanded items ++ structured tail), qvmFrPow, FoldState/foldStep/quotientFold (FOLD_MAIN, FOLD_SELECTOR with y^gap, selector tails, final negation), SelectorFoldConsistent, IdentityCorrespondence, and quotientFold_matches_linearization against computeLinearizationCommitment's reverse fold (R-16/R-19).
imports: Midfall.Lowering.Qvm, Midfall.Halo2.Exec.Linearization, Midfall.Halo2.Exec.VerifyingKey
hazards:
- FOLD_SELECTOR's u8 is the position in plan.sortedSimple, while computeLinearizationCommitment keys by the Lean selector index: the correspondence is a hypothesis (IdentityCorrespondence), not a definitional fact
- identityValues pushes zero for native items (VmCertify.lean:607): never use it as y-position values
- List.modify / List.getD naming in Lean 4.35 (modify f n l)
### formal/Midfall/Lowering/Surface.lean (fields in this scope)
PlanView fields: proofLayout, repack (:= fromProofLayout proofLayout), cfg : GeneratorConfig, accFixedBases : Array (AccFixedBase G₁), hvk : Halo2VerifyingKey, qplan : QuotientProgramPlan, qbuild : QuotientProgramBuild, qext : Option QuotientExternal, plus hypotheses hProofLayout (fromProtocol at 0x64), hRepack, hDirectSharesLayout (P-11), hQbuild (qbuild = buildPlan r qplan (withLimbVmOps true), P-10), hAccBases (artifacts.rs:181-227 shape: "-G" ↦ (P.g₁, negate := true), names ascending), modulusPinned : p = Midfall.Assumptions.r. LeanAccepts := ∃ ms instW, decodeCalldata … = some (ms, instW) ∧ ContractRefAcceptsAcc … instW ms = true.
imports: Midfall.Lowering.Calldata, Midfall.Lowering.Accumulator, Midfall.Lowering.QvmFold, Midfall.Generator.Models, Midfall.Generator.Layout
hazards:
- Surface may import Generator.Vk only if it contains no theorem line AND no theorem file imports Surface (transitive ExponentModel); recommended: keep Vk-dependent facts in Obligations fields and run #print axioms on every theorem that imports Surface
### formal/Midfall/Lowering/Obligations.lean (fields in this scope)
LoweringCorrect fields: qvm_yul_refines (abstract over the Surface frame), qvm_validated_noOOB (validator abstract, two real fault classes + read windows), points_subgroup_checked (semantic, per-run), vkDigest_slot0 (generateBaseVk corollary), repackProof_faithful / encodeCalldata_faithful (P-12 port equalities), accFixedBases_producer, readScheduleAgrees (Exec log widths = plan.slots).
imports: Midfall.Lowering.Surface, Midfall.Yul.Bridge
hazards:
- a Prop-structure with no `theorem` line passes the D-P17 grep even with the exponent model transitively in scope; keep it proof-free

## disagreements
- repack_spec: the PLAN's iff `repackProof = .ok π' ↔ ∃ ms, decodeRust … = some ms ∧ π' = encodeContractProof ms` is FALSE, not merely under-hypothesised. decodeRust runs the whole pipeline and returns none on any Fault, so a proof whose 48/32-byte slots all decode but whose algebra panics (x3 in a point set, kzg/mod.rs:479, R-35; logup.rs:460; i32Abs) repacks successfully with no message list. State the wire-level iff over a pure schedule decoder and the pipeline-level implication decodeRust → repackProof only.
- calldata_canonical: the plan's and survey's '≈ in accumulator mode' fallback is unnecessary. With instances returned as raw Word256 (R-26.7) the calldata is determined exactly by (ms, instW) in both modes; the identity-flag malleability (R-25) is a property of decodeAcc and surfaces only in accWords. Keep calldata_canonical exact and put the normalisation in decodeAcc_injective.
- decodeAcc_injective needs a third hypothesis beyond the survey's eipRoundtrip + Nodup: `codec.toEip 1 = natToBytesBE 0 128`. Without it the identity has a flag-1 encoding and a flag-0 encoding (coordinates of a non-zero toEip 1), both decoding to 1 with different accWords. The orchestrator's accWords form '(0,0,1) for flagged' is right, but the law must be a binder.
- The critic lists a lemma 'every G₁ element is a multiple of P.g₁' as owed for lifting Spec.Lemmas.pairing_reorder to DualMSM.check. It is not needed: at the check level the contract orientation follows from linearity of P.e in the G₂ argument (Additive.ofMul_inv, map_neg) given nG2Prepared = G2_BASE⁻¹ and sG2Prepared = NEG_S_G2⁻¹ (dualMsm_check_iff_contract). The exponent-level lemma is only for Spec-level statements.
- Architecture A proposes decodeCalldata as a Surface field or a now-definition and asks for a decision: define it NOW. No Rust decoder exists, the acceptance checks are all template lines (Halo2Verifier.sol:148, VkLoading.yul:101-112, TranscriptProofParser.yul:63-68/319/382/416, AssemblyHelpers.yul:94-104), so the definition cannot drift from a port; what is owed is its agreement with the Yul partials (vkLoading/transcriptParser specs), not its text.
- Architecture C (logup f_j(x)+β = 0): CONFIRMED divergence. The Yul lookup lowering computes the helper identity h·P − Σ_j prefix_j·suffix_j with NO inversion (yul_emit.rs:508-553; structured native loop quotient.rs:1826-1865 likewise), while Lean (Logup.lean:279, faithful to logup.rs:460) panics. So there exist calldata where the contract computes the true polynomial identity and returns while Lean rejects: the soundness conjunct `obs.isReturn → LeanAccepts` is false without a side condition. Not a security hole (the contract's value is the correct polynomial identity; the Rust shortcut is what is incomplete), but every equivalence conjunct needs `∀ lookup chunk j, compress(input_j)(x) + β ≠ 0` stated through the snapshot API, exactly like x^n ≠ 1 - or Lean's Logup.expressions must be made total in the prefix·suffix form, which is a deliberate deviation from Rust to record.
- Valuation-parametric evaluator: no VmReference.lean refactor is needed to quantify over all ρ. QuotientRefMemory consults its cache FIRST (VmReference.lean:433-438), so a memory pre-populated from ρ on the expression's leaf keys (memOfρ) makes the ported interpreter read ρ; 'no miss' (cache unchanged) is then part of the conclusion. The only care point is the key wrap: evalExprρ must use ((1+t) % 256, addr % 2^32) so token 0xff lands in the literal domain as the KAT tokenDomainU8Wrap shows.
- D-P16 (a)/(b): the critic's bound n < 2^64 - 1 is confirmed necessary (at n = usizeMax with offset = usizeMax the saturating generator accepts and Exec rejects; fixedScalarCount wraps to 2^64 - 12). (c) is unconditional and (d) needs only numLimbBits ≠ 0. No hypothesis on the kind is needed because toExecKind preserves hasCarriedScalars.
- vk_digest: the orchestrator flags Generator/Vk.lean's transitive Instances import. Agreed, and the fix is a split: `feToU256 (bytesToNats (frToRepr x)) = .ok (frWord x)` is a theorem about Encoding+Codec only (no bound on p needed - both sides reduce mod 2^256) and goes in a Vk-free file; the generateBaseVk corollary becomes an Obligations field. More generally: no theorem file may import Midfall.Lowering.Surface if Surface imports Generator.Vk; run #print axioms on every theorem that does.
- Order (D): pull the zero-dependency items ahead of Bridge/finalPairing: D-P16 reconciliation, feToU256_frToRepr, qvmFrModulus_eq_r + qvmToFr, decideBool/eval_addMsm, dualMsm_check_iff_contract and repackedLen_mod32 are all provable in ~3 days with no Yul and unblock the S5, accumulator, calldata and fold statements; finalPairing_spec then consumes dualMsm_check_iff_contract directly.

## open decisions
- R-25 sign-off: adopt accWords as the normalised tail (window from enc.offset, identity-flagged coordinate words zeroed, flags/carried/tail kept) and add `codec.toEip 1 = 128 zero bytes` to decodeAcc_injective's hypotheses. Recommended: adopt.
- decodeAcc_encode scope: restrict to collapsed .pointAndScalar with the contract-convention relabelling negateByTable (plain `= some a` only when no base is negated); record that the .pointPair round trip is false because encodeAccInstances always emits carried scalars and file a kind-aware encoder as a follow-up port. Recommended: adopt, do not patch the encoder silently.
- calldata_canonical: state EXACT (no ≈) over raw Word256 instances in both modes; LeanAccepts takes raw words and lifts. Recommended: adopt (supersedes PLAN.md:489-490's fallback).
- repack_spec: replace the PLAN's iff by repack_spec_wire (pure schedule decoder) + repack_spec_of_decodeRust, since the PLAN form is false for byte-valid proofs whose pipeline panics. Recommended: adopt and note in PLAN 9.5.
- Logup divergence (point C, confirmed: the Yul never inverts, yul_emit.rs:508-553): add a `logupDenomsNonzero` snapshot side condition (∀ chunk j, compress(input_j)(x) + β ≠ 0) to BOTH soundness and completeness conjuncts, or totalise Lean's Logup.expressions to the prefix·suffix form (a recorded deviation from logup.rs:460). Recommended: the side condition now; raise logup.rs:460 upstream as an unnecessary panic.
- Midfall.Halo2.fixedBases "-G" defect (Accumulator.lean:502 inserts the identity): fix by taking the generator (needs [P : AdmissiblePairing] or a `negG : G₁` argument) and re-run the KATs; until then every statement passes `tbl := fb.map (name, base)`. Recommended: fix in a separate Exec patch with its own KAT.
- Tooling: either fix checks.sh (listed sort → `sort -t: -k1,1 -k2,2n`) or keep every new file's sorry tokens in one digit band; add gen_sorry.sh owner arms for Midfall/Lowering/* and Midfall/Assumptions/*. Recommended: fix checks.sh (one line, with sign-off since it is a CI gate).
- D-P17 transitive hazard: rule that no theorem-bearing file imports Generator.Vk (directly or via Surface); Vk-dependent facts (vkDigest_slot0, generateVk witnesses) live as LoweringCorrect fields; extend checks.sh to `#print axioms` every theorem in Lowering/*. Recommended: adopt.
- QVM valuation layer: use the memOfρ pre-populated-cache approach (no VmReference change) rather than generalising VmReference over a memory model. Recommended: memOfρ now; revisit a `QuotientMemModel` refactor only if the Yul composition proof needs per-step memory reasoning.
- Selector bucket key: decide whether `Selector.index = fixed column index` (linearization/verifier.rs:84 indexes fixed_commitments by the key partiallyEvaluateIdentities fills with the selector index) is a pinned Rust invariant or a new review finding; IdentityCorrespondence keeps it as a hypothesis meanwhile.

## proof plan
### M5-0 Scaffolding: Assumptions/Codec.lean (G1CodecLaws), Lowering/AccEncoding.lean, register both in Midfall.lean; add owner arms to scripts/gen_sorry.sh for Midfall/Lowering/* and Midfall/Assumptions/*; decide the checks.sh sort fix vs one-digit-band rule for sorry lines. [M5] est 0.5 day
prereqs: sign-off: SORRY.md owner arms and the checks.sh `sort` mismatch fix (one line)
lemmas:
- toExec_hasCarriedScalars
- noShapeRecognizers_sound-style trivial instances
- G1CodecLaws toy instance over Multiplicative (ZMod 17) as an `example`
risks:
- check_orphans.py fails if a file is not imported from Midfall.lean
- lean_grep.py counts the s-word in doc comments after a primed identifier
evidence: the toy codec `example : G1CodecLaws toyCodec := by decide` shows the law set is satisfiable; a second example shows the degenerate constant-zero codec violates eipShape.
### M5-1 D-P16 reconciliation (a)-(d) with the usize bound and the sentinel counterexample gate. [M5] est 1 day
prereqs: M5-0; #check @Midfall.Halo2.decodeAcc (Accumulator.lean has no olean)
lemmas:
- toExec_coordinateWords
- toExec_fixedPayloadWords
- toExec_fullyCollapsed
- toExec_validFor
- toExec_fixedScalarCount
- usizeSaturatingAdd_of_lt / usizeAdd_eq / usizeSub_eq (Nat.mod_eq_of_lt arithmetic)
- Except.isOk / toOption unfolding of the mutual-block defs via their eq lemmas
risks:
- mutual-block defs may need `AccumulatorEncoding.validateForNumInstances.eq_1` instead of unfold
- `decide` on the 2^64 sentinel example; fallback `rfl` per conjunct
evidence: the `example` at n = usizeMax (generator ok, Exec false) is the perturbation that makes hn load-bearing; fixedScalarCount_wrappingTail_ok is the existing KAT.
### M5-2 Byte lemmas shared by VkDigest, Calldata and Accumulator: natToBytesLowFirst_size, bytesToNatLE_natToBytesLE (n < 256^len), bytesToWordLE_natToBytesLE, bytesFromNats_bytesToNats, natToBytesBE_split64 (wordToBytesBE hi ++ wordToBytesBE lo = natToBytesBE v 64 for v < 2^512), coordOfEip_toEip under eipShape, frToInputBE_cast (w < p → frToInputBE (Nat.cast w) = natToBytesBE w 32). [M5] est 1.5 days
prereqs: M5-0
lemmas:
- feToU256_frToRepr (0.25 day once the above exist)
- wordToBytesBE_bytesToWordBE round trips anchored to keccak256("") and the EIP modulus (R-20 rule: never self-round-trips only)
risks:
- ByteArray extensionality lemmas are thin in core; induction over natToBytesLowFirst.go
evidence: feToU256_frToRepr fails under a BE read at x = 1; R-20-style anchor: `bytesToWordBE (keccak256 Bytes.empty bytes) = 0xc5d2…a470` as a KAT next to the lemma.
### M5-3 accWords + decodeAcc_injective. [M5] est 2 days
prereqs: M5-2; Assumptions/Codec.lean
lemmas:
- decodeAccCoord_inj (packing-canonical words are determined by the reconstructed v)
- loadAccPoint_flag0_bytes (bytes = wordToBytesBE xhi ++ xlo ++ yhi ++ ylo)
- loadAccPoint_flag1 (any coordinates ↦ 128 zero bytes)
- accMapInsert_fold_lookup_nodup (tail word j recoverable from the map under Nodup names)
- Nat.cast_injOn_lt_p (ZMod.val_natCast)
- identity_flag_forced (toEip 1 = zeros ⇒ flag 0 cannot decode to 1, via Accumulator.lean:409)
risks:
- decodeAcc's `-s` elaboration (Accumulator.lean:987) unverified
- Array.extract/getD index arithmetic in accWords
evidence: accIdentityKats_ok is the unprojected counterexample; a duplicate-name fb with tails [1,2]/[3,2] is the Nodup counterexample; a codec with toEip 1 = natToBytesBE 7 128 is the toEip_one counterexample.
### M5-4 decodeAcc_encode (collapsed .pointAndScalar) + negateByTable corollary. [M5] est 2 days
prereqs: M5-2; M5-3 lemmas on loadAccPoint
lemmas:
- encodeAccCoordWords_packingOk
- biFromLimbs_biToLimbs (v < 2^(7·56))
- loadAccCoordShifted_encode
- decodeAccCoord_encode (x < p ⇒ some (x / 2^256, x % 2^256))
- loadAccPoint_encode_nonId / _id
- accMapInsert_fold_sorted_id (strictly ascending input reproduced)
- fixedScalarCount_exact (size = offset + 12 + tail)
risks:
- the (0,0) rejection requires eipShape's ¬(x=0∧y=0) clause; on the real curve y² = x³ + 4 so (0,0) is off-curve, but over abstract G₁ it is a binder
- pointPair round trip is false (encoder emits carried scalars unconditionally); a kind-aware encoder is a separate port
evidence: a KAT with pairwise distinct scalars (tests.rs:2063-2073 shape) distinguishes point/slot shifts; a negate base with nonzero tail scalar distinguishes `= some a` from `= some (negateByTable fb a)`.
### M5-5 Algebra for S5 and the pairing lift: decideBool_eq_true_iff, MSMKZG.eval_fromBase/eval_scale/eval_addMsm (lockstep), gsmul lemmas (gsmul_neg_eq_inv: (-s)•B = s•B⁻¹, the fixedBases "-G" bridge), dualMsm_check_iff_contract, batched_complete, batched_atMostOneRoot (field argument on ZMod p-module, no card lemma). [M5 (statements) / M9 (S5 proofs may land now)] est 1.5 days
prereqs: none beyond Exec Kzg/Msm.lean (built)
lemmas:
- msmSpecific_append (lockstep)
- Additive.toMul_eq_one_iff
- smul_left_injective over a field for y ≠ 0
risks:
- MSMKZG.eval's `scalars.toList = [1]` shortcut needs a case split in eval_addMsm
evidence: dualMsm_scale_check style: `example` on the exponent model (Instances-only gate) where the unbatched check fails and alpha = 2 still fails the batched one, plus the hn-dropped orientation counterexample.
### M5-6 ContractRefAcceptsAcc, contractRefAcceptsAcc_none, contractRef_acc_complete; update LeanAccepts in Surface to use it over raw instance words. [M5] est 1 day
prereqs: M5-5; Surface.accFixedBases shape hypothesis (artifacts.rs:181-227: "-G" ↦ (P.g₁, true), names ascending)
lemmas:
- prepareMsgs_Wf (owed: prepareMsgs outputs have lockstep MSM channels) - take as hypothesis until proved
- KzgAcc.check_unfold (eval_fromBase twice)
risks:
- Midfall.Halo2.fixedBases "-G" defect must stay out of every statement until fixed
evidence: double-negation perturbation (table AND decoder negating) flips batchedCheck on a KAT with a negate base.
### M5-7 Calldata definitions and layout lemmas: WireSlot/slots, encodeContractProof, repackProof/decodeWire, encodeCalldataRaw/encodeCalldata/calldataOf, decodeCalldata; repackedLen_mod32, sum_commitmentReadGroups, proofLen_eq_repackedLen; poseidon-dump KAT (4484 bytes, 0x10e0, 0x1140). [M5] est 1.5 days
prereqs: M5-0
lemmas:
- ProofCalldataLayout.fromProtocol section tiling (induction over takeCommitmentSection)
- List.sum_filter_ne_zero
risks:
- fromProtocol is a long do-block over Except Fault; the tiling lemma needs the cursor invariant at each of the 10 steps
evidence: repackedProofLayout_widthsDiffer_ok and commitmentReadGroups_disagreeWhenHandBuilt_ok are the existing perturbations; the dump KAT pins the head words to an artifact we did not produce.
### M5-8 calldata_roundtrip, calldata_canonical, repack_spec_wire, repack_spec_of_decodeRust (+ decodeRust_decodeWire). [M5] est 5 days
prereqs: M5-2; M5-7; transcript_log_concat (Transcript.read appends (width, repr) and advances pos; shared with the provable restatement of verifyNative_iff_msgs); Obligations.readScheduleAgrees (Exec log widths = plan.slots) as a hypothesis
lemmas:
- decodeSlots_encode (induction over slots with cursor arithmetic)
- cdWord_append_left/right
- g1WordsOk_of_eipShape
- repackProof_foldl_spec
risks:
- decodeRust's log is produced inside StateT over the whole pipeline; extracting 'the consumed prefix equals the concatenated reprs' is the same lemma the frozen verifyNative_iff_msgs needs and is the largest single item
evidence: R-20 rule: a KAT compares calldataOf on a fixed (ms, inst) against the dump bytes, not against our own decoder; the LE-scalar perturbation fails at s = 1.
### M6-0 QVMFr ↔ Fr r bridge and the valuation layer: qvmFrModulus_eq_r, qvmToFr_{add,mul,neg,injOn}, Valuation/memKey/evalExprρ/memOfρ/NoMiss/CacheConsistent, evalQuotientExpr_memOfρ, derive_hit lemma. [M6] est 1.5 days
prereqs: none (VmReference/VmTypes/VmBuilder/VmCertify import no Instances)
lemmas:
- quotientRefMemoryCacheGet_memOfρ (find? on the mapped list)
- QuotientRefMemory.derive_hit (cache hit returns cached value and the same memory)
- CacheConsistent_new (fresh memory)
risks:
- `decide` on the two 255-bit literals (fallback rfl)
- List.find? with duplicate keys in memOfρ: first match wins, consistent by construction
evidence: token 0xff: evalExprρ with an unwrapped key disagrees with the interpreter (existing KAT tokenDomainU8Wrap_releaseProfile_ok).
### M6-1 Shape denotations and RecognizersSound; noShapeRecognizers_sound; denotation ↔ byte-decoder lemmas (limbLinearForm/limbRowForm/limbPairwiseForm/modarith7Form over memOfρ equal denote* when their pointers are in S). [M6] est 2.5 days
prereqs: M6-0
lemmas:
- foldRangeIdxM_induction (R3 combinator)
- limbLinearForm_memOfρ
- limbRowForm_memOfρ
- limbPairwiseForm_memOfρ (56 reads, 14 addresses)
- modarith7Form_memOfρ (count headers, cond last)
risks:
- (slot, ptr) vs (ptr, slot) operand order between the mem block and the standalone affine term (VmReference.lean:636 doc) - a denotation must follow the decoder, not the builder
- FLAG_CONST absent ↔ constant = 0 must be checked in the builder (tryEmitModarith7Shape)
evidence: denotations evaluated on the existing VmReference fixtures must reproduce the byte decoders' values; a swapped (slot, ptr) order is caught by a fixture with slot ≠ ptr.
### M6-2 Builder correctness core: emit appends only, stackDepth = real stack height, emitExpr never emits stream opcodes, emitExpr_correct by fuel induction with the four peephole cases under RecognizersSound (pow5, modarith7, limb family, decomposition, AFFINE_SUM reordering, tryEmitAddProduct swap), compaction preserves value and respects segments, fold byte placement (finalizedIdentitySegment of identityExpr output). [M6] est 7 days
prereqs: M6-1
lemmas:
- identityExpr_bytes_append
- emitFuel_adequate (8·(nodeCount+1) never binds)
- compactQuotientRuns_segments
- compactQuotientRuns_value
- finalizedIdentitySegment_identityExpr
- quotientOpLen_of_emitted
risks:
- the mutual block VmBuilder.lean:700-894 with ~40 panic sites; proofs case-split on `.ok` hypotheses
- compaction's AFFINE_SUM reorders linear-before-product terms: value preservation needs commutativity in QVMFr (qvmToFr homomorphism + ring)
evidence: certifyQuotientBuildsAgree (optimized vs baseline) is the existing executable witness that the recognizer paths and the generic path agree on the fixtures; the per-identity theorem must reproduce exactly those fixtures as `example`s.
### M6-3 Assemble qvm_compile_correct_identity, buildItems/buildPlan driver, qvm_compile_correct_certifier/_program, builder_segments_total. [M6] est 3 days
prereqs: M6-2
lemmas:
- identitySegment_of_emitted (walk stops at the fold byte because expression bytes contain no fold/native opcode)
- checkFold_of_buildItems (positional check succeeds by construction: u24 = idx·65536 ||| gap)
- certifyItemWalk_induction over plan.items with cursor arithmetic
risks:
- native markers' byte lengths (quotientOpLen) and the u16 native index
evidence: threeIdentityBuild/threeIdentityPlan (VmCertify.lean:855-870) become `example`s of the theorem; perturbing the plan's gap (5 → 4) must make hbuild/checkFold fail.
### M6-4 Whole-stream fold: globalIdentities, quotientFold, SelectorFoldConsistent, IdentityCorrespondence, quotientFold_matches_linearization. [M6] est 3 days
prereqs: M6-0; Exec Linearization.lean (built)
lemmas:
- horner_reverse (Σ v_i y^(m-1-i) as a left fold)
- groupedAdd_as_sum (sorted assoc list = finite sum keyed by Option Nat)
- bucket_horner_with_gaps (gap/tail exponents reproduce y^(m-1-i))
- sortedSimple_order (ascending s = ascending column keys)
risks:
- R-16 ordering traps are inside partiallyEvaluateIdentities (permutation rev().skip(1), last-set second, trash left fold): the correspondence hypothesis must be discharged by P-10's plan producer, not here
- Selector.index vs fixed-column index at linearization/verifier.rs:84 is a Rust invariant to pin (potential review item)
evidence: a fixture with ≥ 2 main and ≥ 2 selector identities interleaved (R-30 rule); off-by-one gap perturbation flips the bucket by a factor y.
### M6-5 Statement-only items: EvaluatorFrame/FrameWellFormed/frameValuation in Surface, qvm_yul_refines and the validator-form noOOB as Obligations fields, direct_correct placeholder for M10. [M6 (statements); proofs blocked] est 1 day for the statements
prereqs: Midfall.Yul.Bridge (P-BR); P-09h / P-13 (QuotientNumeratorBlock.yul + Halo2QuotientEvaluator.sol as Block EVM.Op); P-09e (validateQuotientProgramOperands, OperandModel)
lemmas:
risks:
- the frame contains the program: FrameWellFormed must pin the VK window or the field is false
- gas() under ExternalGas.any blocks determinism; the evaluator call is staticcall(gas(), …)
evidence: adversarial-frame counterexample ([PUSH_CONST 0, FOLD_MAIN] bytecode) recorded next to FrameWellFormed as the reason for the VK-window conjunct.

## declarations
### G1CodecLaws  (structure; statable-now; M5) — formal/Midfall/Assumptions/Codec.lean
```lean
namespace Midfall.Assumptions
open Midfall

/-- The G1 codec laws the accumulator and calldata statements consume. R-34: no Lean
    instance proves any of them and the BLS codec lives under Instances/, so each law is
    a binder. The two round trips are the tree's decoder-first properties
    (Common/Codec.lean:106, :113); the encoder-first law was deliberately removed from
    `G1Codec` (Codec.lean:97-105) and is needed only by the accumulator and calldata
    round trips, where the encoder is OUR `asPublicInputPoint`/`encodeContractProof`. -/
structure G1CodecLaws {G₁ : Type} [Group G₁] (c : G1Codec G₁) : Prop where
  eipRoundtrip : c.eipRoundtrip
  compressedRoundtrip : c.compressedRoundtrip
  /-- encoder-first: needed by decodeAcc_encode and calldata_roundtrip -/
  ofEip_toEip : ∀ Q : G₁, c.ofEip? (c.toEip Q) = some Q
  /-- EIP-2537 shape with in-field, non-(0,0) coordinates (AssemblyHelpers.yul:94-104,
      AccumulatorHelpers.yul:152-157 reject (0,0) under flag 0) -/
  eipShape : ∀ Q : G₁, Q ≠ 1 → ∃ x y : Nat, x < pBase ∧ y < pBase ∧ ¬ (x = 0 ∧ y = 0) ∧
    c.toEip Q = natToBytesBE 0 16 ++ natToBytesBE x 48 ++ natToBytesBE 0 16 ++ natToBytesBE y 48
  /-- identity ↔ 128 zero bytes (AccumulatorHelpers.yul:137-140, Accumulator.lean:405) -/
  toEip_one : c.toEip 1 = natToBytesBE 0 128
  compressedWidth : ∀ Q : G₁, (c.toCompressed Q).size = g1CompressedWidth

end Midfall.Assumptions
```
hypotheses:
- [Group G₁] - only to name (1 : G₁); no DecidableEq binder (D-P7)
non-vacuity: toEip := fun _ => natToBytesBE 0 128 violates eipShape's ¬(x=0∧y=0) and ofEip? := fun _ => none violates ofEip_toEip; a toy codec on Multiplicative (ZMod 17) (Q ≠ 1 ↦ x := Q.val, y := 1) satisfies all fields by `decide`, so the structure is inhabited.

### toExec (+ toExecKind, toExec_hasCarriedScalars)  (def; provable-now; M5) — formal/Midfall/Lowering/AccEncoding.lean
```lean
namespace Midfall.Lowering
open Midfall Midfall.Halo2

/-- D-P16: kind map, generator → Exec stand-in. -/
def toExecKind : Midfall.Generator.AccumulatorEncodingKind → Midfall.Halo2.AccumulatorEncodingKind
  | .pointAndScalar => .pointAndScalar
  | .pointPair => .pointPair

/-- D-P16: the faithful generator encoding viewed as the Exec stand-in `decodeAcc` and
    `encodeAccInstances` are typed over. -/
def toExec (e : Midfall.Generator.AccumulatorEncoding) : Midfall.Halo2.AccumulatorEncoding :=
  { offset := e.offset, numLimbs := e.numLimbs, numLimbBits := e.numLimbBits,
    kind := toExecKind e.kind }

theorem toExec_hasCarriedScalars (e : Midfall.Generator.AccumulatorEncoding) :
    (toExec e).hasCarriedScalars = e.hasCarriedScalars := by
  obtain ⟨_, _, _, k⟩ := e; cases k <;> rfl
```
hypotheses:
non-vacuity: a kind map that swaps the constructors makes toExec_hasCarriedScalars fail by rfl on .pointPair.

### toExec_coordinateWords (d) / toExec_fixedPayloadWords  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/AccEncoding.lean
```lean
/-- D-P16 (d): the generator's coordinate-word count agrees with the Exec stand-in
    whenever the generator does not hit its api.rs:104 division-by-zero panic. -/
theorem toExec_coordinateWords (e : Midfall.Generator.AccumulatorEncoding)
    (h : e.numLimbBits ≠ 0) :
    e.coordinateWords = .ok (toExec e).coordinateWords := by sorry

theorem toExec_fixedPayloadWords (e : Midfall.Generator.AccumulatorEncoding)
    (h : e.numLimbBits ≠ 0) :
    e.fixedPayloadWords = .ok (toExec e).fixedPayloadWords := by sorry
```
hypotheses:
- h : e.numLimbBits ≠ 0 - necessary: Generator panics (ApiFault.panic api.rs:104) while Exec's `max 1 (254/0)` answers (D-P16 item 4, the masked panic)
non-vacuity: at numLimbBits = 0 the two sides differ (panic vs 7 words), so dropping h makes the statement false; at 7x56 both give 2 (accLayoutKats_ok).

### toExec_fullyCollapsed (c)  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/AccEncoding.lean
```lean
/-- D-P16 (c), unconditional: the usize::MAX sentinel at api.rs:137 makes the tail bound
    unfireable, so only the shape check remains on both sides. -/
theorem toExec_fullyCollapsed (e : Midfall.Generator.AccumulatorEncoding) :
    e.fullyCollapsedPublicInputWords.toOption = (toExec e).fullyCollapsedPublicInputWords := by
  sorry
```
hypotheses:
non-vacuity: an Exec stand-in that forgot limbShapeOk would return some 12 for numLimbs = 8 where the generator errors.

### toExec_validFor (a)  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/AccEncoding.lean
```lean
/-- D-P16 (a). The bound is necessary (see the example below): the generator's
    saturating add (api.rs:160) accepts at n = usize::MAX what Exec's unbounded ≤ rejects. -/
theorem toExec_validFor (e : Midfall.Generator.AccumulatorEncoding) (n : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    (e.validateForNumInstances n).isOk = (toExec e).validFor n := by sorry

/-- Counterexample gate for the bound (hazard 3 / F-3). -/
example :
    ((Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56).validateForNumInstances
        Midfall.Generator.usizeMax).isOk = true ∧
    (toExec (Midfall.Generator.AccumulatorEncoding.new Midfall.Generator.usizeMax 7 56)).validFor
        Midfall.Generator.usizeMax = false := by decide
```
hypotheses:
- hn : n < 2^64 - 1 - necessary (critic/D-P16): at n = usizeMax with offset = usizeMax the saturated sum ≤ n but offset + 12 > n
non-vacuity: the `example` is the concrete violation at the sentinel; if `decide` stalls on the mutual-block defs, `rfl` on each conjunct is the fallback (both are closed Bool terms).

### toExec_fixedScalarCount (b)  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/AccEncoding.lean
```lean
/-- D-P16 (b): under the usize bound the wrapping usizeAdd/usizeSub (api.rs:177) equal
    plain Nat arithmetic, and the pointPair tail rejection is the same test. -/
theorem toExec_fixedScalarCount (e : Midfall.Generator.AccumulatorEncoding) (n t : Nat)
    (hn : n < Midfall.Generator.usizeMax) :
    e.fixedScalarCount n = .ok t ↔ (toExec e).fixedScalarCount n = some t := by sorry
```
hypotheses:
- hn : n < 2^64 - 1 - necessary: fixedScalarCount_wrappingTail_ok (Api.lean) exhibits tail 2^64-12 vs Exec none at the sentinel
non-vacuity: with the wrap, Generator gives 2^64-12 where Exec gives none; the existing KAT is the witness.

### accWords  (def; statable-now; M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- R-25 projection of an instance array to the accumulator tail the decoder actually
    reads: the window from `enc.offset` to the end, with the coordinate words of an
    identity-flagged point zeroed (AccumulatorHelpers.yul:130-141 never reads them).
    Flag words, carried scalars and tail scalars are kept verbatim. Point slots sit at
    0 and pointWords + (1 if carried) inside the window (decodeAcc, Accumulator.lean:965-968). -/
def accWords (enc : Midfall.Halo2.AccumulatorEncoding) (inst : Array Word256) : Array Word256 :=
  let tail := inst.extract enc.offset inst.size
  let cw := enc.coordinateWords
  let rhsSrc := enc.pointWords + (if enc.hasCarriedScalars then 1 else 0)
  let zeroCoords (a : Array Word256) (src : Nat) : Array Word256 :=
    if a.getD (src + 2 * cw) 0 = 1 then
      (List.range (2 * cw)).foldl (fun acc j => arraySetD acc (src + j) 0) a
    else a
  zeroCoords (zeroCoords tail 0) rhsSrc
```
hypotheses:
non-vacuity: without the window `inst.extract`, two arrays differing below enc.offset decode identically and injectivity fails; without zeroing, accIdentityKats_ok's pair (coords 12345/54321 under flag 1) is a counterexample.

### decodeAcc_injective  (theorem-sorry; statable-now; M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- PLAN 9.5 decodeAcc_injective in its R-25 form: two instance arrays that decode to the
    same accumulator agree on the normalised tail. -/
theorem decodeAcc_injective {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁]
    (enc : Midfall.Halo2.AccumulatorEncoding) (codec : G1Codec G₁)
    (hrt : codec.eipRoundtrip) (hone : codec.toEip 1 = natToBytesBE 0 128)
    (fb : Array (AccFixedBase G₁)) (hnodup : (fb.toList.map AccFixedBase.name).Nodup)
    (i₁ i₂ : Array Word256) (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (h₁ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₁ = some a)
    (h₂ : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) enc codec fb i₂ = some a) :
    accWords enc i₁ = accWords enc i₂ := by sorry
```
hypotheses:
- hrt : codec.eipRoundtrip - both flag-0 slots decode to the same point L, so their 128 rebuilt bytes are both toEip L (R-25 hypothesis list)
- hone : codec.toEip 1 = 128 zero bytes - NEW, not in the survey: without it the identity could be encoded with flag 1 (tail A) and with flag 0 plus the non-zero bytes toEip 1 (tail B); both decode to 1 but accWords differ in the flag word. With it, the flag-0 route gives decoded (0,0), rejected at Accumulator.lean:409
- hnodup - accMapInsert overwrites duplicate names (Accumulator.lean:466-474), so a repeated name drops a tail word and two tails differing there decode alike (R-25)
- no p ≤ 2^256 bound needed: tail/carried words are checked < p before Nat.cast, and Nat.cast is injective below p
non-vacuity: accIdentityKats_ok is a counterexample to the unprojected form; dropping hnodup: fb = #[⟨"a",B,false⟩,⟨"a",B,false⟩], tails [1,2] and [3,2] decode to the same a.

### negateByTable + decodeAcc_encode  (theorem-sorry; statable-now; M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- Contract-convention relabelling (R-26.3): a base whose generated entry carries
    `negate` holds the negated scalar (AccumulatorHelpers.yul:322-326). -/
def negateByTable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    (fb : Array (AccFixedBase G₁)) (a : KzgAcc (Fr p) G₁ G₂ Gₜ) : KzgAcc (Fr p) G₁ G₂ Gₜ :=
  let neg (n : String) : Bool := fb.any (fun b => b.name == n && b.negate)
  { a with rhs := { a.rhs with fixedBaseScalars :=
      a.rhs.fixedBaseScalars.map (fun (n, s) => (n, if neg n then -s else s)) } }

/-- PLAN 9.5 decodeAcc_encode, restricted to the only shape the contract can read
    (R-26.2): a collapsed point-and-scalar accumulator, prefixed by `enc.offset` words. -/
theorem decodeAcc_encode {p : ℕ} [Fact (Nat.Prime p)] (hp : p < 2 ^ 256)
    {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
    [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
    [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]
    (enc : Midfall.Generator.AccumulatorEncoding)
    (hkind : enc.kind = Midfall.Generator.AccumulatorEncodingKind.pointAndScalar)
    (hshape : (toExec enc).limbShapeOk = true)
    (codec : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws codec)
    (L R : G₁) (sL sR : Fr p) (tail : Array (String × Fr p))
    (hsorted : (tail.toList.map Prod.fst).Sorted (· < ·))
    (fb : Array (AccFixedBase G₁))
    (hnames : fb.toList.map AccFixedBase.name = tail.toList.map Prod.fst)
    (prefix : Array Word256) (hpre : prefix.size = enc.offset) :
    let a : KzgAcc (Fr p) G₁ G₂ Gₜ :=
      { lhs := { bases := #[L], scalars := #[sL], fixedBaseScalars := #[] },
        rhs := { bases := #[R], scalars := #[sR], fixedBaseScalars := tail } }
    decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) codec fb
        (prefix ++ encodeAccInstances (toExec enc) codec a) = some (negateByTable fb a) := by
  sorry

/-- The PLAN's literal `= some a` holds exactly when no base is negated. -/
theorem decodeAcc_encode_noNeg (… same binders …) (hneg : ∀ b ∈ fb.toList, b.negate = false) :
    decodeAcc … = some a := by sorry
```
hypotheses:
- hp : p < 2^256 - (frWord s).toNat = s.val needs no BitVec wrap (frWord doc, Accumulator.lean:433)
- hkind = pointAndScalar - encodeAccInstances emits the two carried scalars unconditionally (Accumulator.lean:640), so for .pointPair the tail is 2 words long and fixedScalarCount returns none: the round trip is FALSE for pointPair (survey, new finding)
- hshape - fixedScalarCount needs validFor
- hc.ofEip_toEip - the decoder rebuilds toEip L and must recover L; hc.eipShape - the rebuilt bytes wordToBytesBE hi ++ lo per coordinate equal toEip L only for the 16‖48 shape with x,y < p (range checks Accumulator.lean:368-370) and (x,y) ≠ (0,0) (line 409); hc.toEip_one - identity encodes under flag 1 and decodes via ofEip? of 128 zero bytes
- hsorted - decodeAcc rebuilds the map with accMapInsert in fb order; only a strictly ascending tail is reproduced verbatim (AccMsm's BTreeMap invariant is not in the type)
- hnames - fb.size = tail count and name-by-name pairing (artifacts.rs:225 sorts by name)
- hpre - decodeAcc reads at enc.offset
non-vacuity: a decoder reading scalar-before-point, or omitting the coordinate-minus-one shift, fails on a KAT with pairwise distinct scalars (lowering/tests.rs:2063-2073 style); with hneg dropped and one negate base the two sides differ by the sign of that tail scalar.

### decideBool_eq_true_iff / MSMKZG.eval_addMsm / eval_scale / eval_fromBase  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
theorem decideBool_eq_true_iff {α : Type} {a b : α} (d : Decidable (a = b)) :
    decideBool d = true ↔ a = b := by
  cases d <;> simp [decideBool, *]

/-- Additivity of the MSM value; msmSpecific zips with truncation (Msm.lean:52-56), so
    lockstep lengths are required (MSMKZG.Wf minus the labels conjunct). -/
theorem MSMKZG.eval_addMsm {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    [PrimeOrderWith G₁ p] [Module (ZMod p) (Additive G₁)]
    (m n : MSMKZG (Fr p) G₁) (hm : m.scalars.size = m.bases.size)
    (hn : n.scalars.size = n.bases.size) :
    (m.addMsm n).eval = m.eval * n.eval := by sorry

theorem MSMKZG.eval_fromBase … (Q : G₁) : (MSMKZG.fromBase Q).eval = Q := by simp [MSMKZG.eval, MSMKZG.fromBase]
theorem MSMKZG.eval_scale … (m) (hm) (c : Fr p) : (m.scale c).eval = gsmul c m.eval := by sorry
```
hypotheses:
- hm/hn lockstep - a scalars/bases length mismatch truncates and additivity fails (Wf is not carried in the type, Msm.lean:68)
non-vacuity: m := {scalars := #[1,1], bases := #[B]} breaks eval_addMsm: the second scalar is silently dropped.

### batched_complete / batched_atMostOneRoot (S5)  (theorem-sorry; statable-now; M5 (S5 statements), M9 (proofs)) — formal/Midfall/Lowering/Accumulator.lean
```lean
section S5
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Both equations hold ⇒ the alpha-batched equation holds, for every alpha (bilinearity). -/
theorem batched_complete (params : ParamsVerifierKZG G₁ G₂) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁))
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hd : DualMSM.check d params = true) (ha : KzgAcc.check a params tbl = true) (alpha : Fr p) :
    batchedCheck params alpha d a tbl = true := by sorry

/-- If either equation fails, at most one alpha makes the batched one pass. -/
theorem batched_atMostOneRoot (params) (d) (a) (tbl) (hWf : …)
    (hbad : DualMSM.check d params = false ∨ KzgAcc.check a params tbl = false)
    (alpha beta : Fr p) (hα : batchedCheck params alpha d a tbl = true)
    (hβ : batchedCheck params beta d a tbl = true) : alpha = beta := by sorry
end S5
```
hypotheses:
- hWf - eval_addMsm needs lockstep lengths; an owed lemma shows prepareMsgs outputs satisfy it (take as hypothesis until then)
- no alpha ≠ 0 side condition: completeness is linear in alpha; alphaOf maps 0 ↦ 1 anyway
non-vacuity: atMostOneRoot: with Y := e(aL,sG2)+e(aR,nG2) ≠ 0 (field ZMod p-module), alpha•Y = beta•Y ⇒ alpha = beta; if Y = 0 then X ≠ 0 and no alpha works. complete: a check that forgot the alpha scaling on one channel fails for alpha = 2 on a KAT over the exponent model (Instances-only gate).

### contractPairingHolds + dualMsm_check_iff_contract  (theorem-sorry; provable-now; M7 (finalPairing_spec consumer), provable M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- The contract orientation at the CHECK level: e(PAIRING_RHS, G2)·e(PAIRING_LHS, NEG_S_G2) = 1
    (swap at FinalPairing.yul:88; layout AssemblyHelpers.yul:284-287). -/
def contractPairingHolds (g2 negSG2 : G₂) (lhs rhs : G₁) : Prop :=
  P.e (Additive.ofMul rhs) (Additive.ofMul g2) + P.e (Additive.ofMul lhs) (Additive.ofMul negSG2) = 0

/-- The lift of Spec.Lemmas.pairing_reorder to DualMSM.check: no exponent model and no
    "every point is a multiple of g₁" lemma is needed, only linearity in the G₂ slot. -/
theorem dualMsm_check_iff_contract (d : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (g2 negSG2 : G₂) (hn : params.nG2Prepared = g2⁻¹) (hs : params.sG2Prepared = negSG2⁻¹) :
    DualMSM.check d params = true ↔ contractPairingHolds g2 negSG2 d.left.eval d.right.eval := by
  sorry  -- decideBool_eq_true_iff, Additive.toMul_eq_one, Additive.ofMul_inv, map_neg, neg_add, neg_eq_zero, add_comm
```
hypotheses:
- hn : nG2Prepared = g2⁻¹ - R-4: ofParams uses g2⁻¹, read uses g2Gen⁻¹; the contract embeds G2_BASE = params.g2 (Vk.lean:802-815)
- hs : sG2Prepared = negSG2⁻¹ - NEG_S_G2_BASE = sG2⁻¹ is embedded (Vk.lean)
non-vacuity: with hn dropped (nG2Prepared := g2) the two sides are e(l,sG2)e(r,g2) vs e(r,g2)e(l,-sG2), unequal on the exponent model for l = r = g₁.

### ContractRefAcceptsAcc (+ _none)  (def; statable-now; M5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- The lift of a canonical calldata word; total, used only on words the decoder checked < p. -/
def liftWord {p : ℕ} [Fact (Nat.Prime p)] (w : Word256) : Fr p := Nat.cast w.toNat

/-- PLAN 9.5 ContractRef.accepts with the accumulator arm, over RAW instance words so the
    `≥ r` rejections of validate_public_accumulator stay visible (R-26.7). `fb` is the
    generated positive-base table (artifacts.rs:181-227), passed in because the tree's
    `fixedBases` "-G" entry is the identity (Accumulator.lean:502, defect). -/
def ContractRefAcceptsAcc (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (acc : Option Midfall.Generator.AccumulatorEncoding) (fb : Array (AccFixedBase G₁))
    (instW : Array Word256) (ms : List (Msg (Fr p) G₁)) : Bool :=
  let inst : Array (Fr p) := instW.map liftWord
  match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
  | .error _ => false
  | .ok d =>
    match acc with
    | none => DualMSM.check d params
    | some enc =>
      let tbl := fb.map (fun b => (b.name, b.base))
      match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW with
      | none => false
      | some a =>
        let (accL, accR) := a.fullyCollapse tbl
        batchedCheck params
          (alphaOf (p := p) H (frWord vk.transcriptRepr) E.g1 d.left.eval d.right.eval accL accR)
          d a tbl

theorem contractRefAcceptsAcc_none (E H params vk fb instW ms) :
    ContractRefAcceptsAcc E H params vk none fb instW ms =
      Midfall.Lowering.ContractRefAccepts E H params vk (instW.map liftWord) ms := by
  unfold ContractRefAcceptsAcc ContractRefAccepts; cases prepareMsgs … <;> rfl
```
hypotheses:
- vk_digest is frWord vk.transcriptRepr (R-1: imported, importer-relative), tied to the deployed word by feToU256_frToRepr
- alphaOf argument order (kzgLhs kzgRhs accLhs accRhs) with kzgLhs := d.left.eval = PAIRING_LHS (= pi) per FinalPairing.yul:21-26
non-vacuity: swapping d.left/d.right in alphaOf changes the hashed preimage and every accept/reject decision on an exponent-model KAT; _none is the required rfl-level agreement with the existing no-acc arm.

### contractRef_acc_complete  (theorem-sorry; statable-now; M5 statement, proof after S5) — formal/Midfall/Lowering/Accumulator.lean
```lean
/-- PLAN 9.5 contractRef_acc_complete (R-26.4 direction only): Rust-accepts plus a
    decodable, separately valid accumulator ⇒ ContractRef accepts. -/
theorem contractRef_acc_complete (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (enc : Midfall.Generator.AccumulatorEncoding) (fb : Array (AccFixedBase G₁))
    (instW : Array Word256) (ms : List (Msg (Fr p) G₁)) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (hpre : prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk (instW.map liftWord) ms = .ok d)
    (hWf : d.left.scalars.size = d.left.bases.size ∧ d.right.scalars.size = d.right.bases.size)
    (hv : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk (instW.map liftWord) ms = .ok ())
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hdec : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW = some a)
    (hchk : KzgAcc.check a params (fb.map (fun b => (b.name, b.base))) = true) :
    ContractRefAcceptsAcc E H params vk (some enc) fb instW ms = true := by
  sorry  -- unfold; rw [hpre, hdec]; exact batched_complete … hWf (check from hv) hchk _
```
hypotheses:
- hpre/hWf - names d and gives eval_addMsm its lockstep lengths (owed prepareMsgs-Wf lemma)
- hdec premise - the contract curve/subgroup-checks accumulator points Rust never validates, so the implication is one-way (R-26.4)
- no hypothesis on alpha: batched_complete is alpha-free
non-vacuity: a ContractRefAcceptsAcc that negated the tail twice (table AND decoder) makes a.check and batchedCheck disagree on a KAT with a negate base and nonzero tail scalar.

### feToU256_frToRepr (vk_digest = frWord vk.transcriptRepr)  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/VkDigest.lean
```lean
/-- The deployed VK_DIGEST word (Generator/Vk.lean:763, `feToU256 (bytesToNats (frToRepr
    vk.transcriptRepr))`) is `frWord vk.transcriptRepr`. No bound on p: natToBytesLE
    keeps the low 32 bytes and BitVec.ofNat reduces mod 2^256, so both sides agree even
    when x.val ≥ 2^256. Stated over Encoding.feToU256 so this file does not import
    Generator.Vk (transitive Instances.ExponentModel, D-P17). -/
theorem feToU256_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (x : Fr p) :
    Midfall.Generator.feToU256 (Midfall.Generator.bytesToNats (frToRepr x)) = .ok (frWord x) := by
  sorry  -- natToBytesLowFirst_size, bytesFromNats_bytesToNats, bytesToWordLE_natToBytesLE

/-- Obligations field (needs Generator.Vk; no theorem line):
    vkDigest_slot0 : ∀ codecs inputs hvk, generateBaseVk codecs inputs = .ok hvk →
      hvk.constants.head? = some ("vk_digest", frWord inputs.vk.transcriptRepr) -/
```
hypotheses:
non-vacuity: a BE read (bytesToWordBE) of the LE repr fails at x = 1 (gives 2^248 ≠ 1).

### WireSlot / Msg.slot / RepackedProofLayoutPlan.slots / encodeContractProof  (def; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
namespace Midfall.Lowering
open Midfall Midfall.Halo2 Midfall.Generator (RepackedProofLayoutPlan ProofCalldataLayout RepackError)

inductive WireSlot | g1 | fr deriving DecidableEq, Repr

def Msg.slot {F G : Type} : Msg F G → WireSlot
  | .g1 _ => .g1
  | .fr _ => .fr

/-- The repack walk order (calldata.rs:109-126) = the transcript read order. -/
def RepackedProofLayoutPlan.slots (plan : RepackedProofLayoutPlan) : List WireSlot :=
  List.replicate plan.prefixG1Count .g1 ++ List.replicate plan.numEvals .fr ++ [.g1] ++
    List.replicate plan.numPointSets .fr ++ [.g1]

/-- Contract-side bytes of one message: EIP-2537 padded point (calldata.rs:74-85) or
    32-byte BE scalar (scalar_le_to_be_word). -/
def msgContractBytes {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) :
    Msg (Fr p) G₁ → Bytes
  | .g1 Q => c.toEip Q
  | .fr s => frToInputBE s

/-- PLAN 9.5 encodeContractProof: layout-independent, the concatenation of the messages'
    contract bytes (the schedule is carried by `ms` itself). -/
def encodeContractProof {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁)
    (ms : List (Msg (Fr p) G₁)) : Bytes :=
  ms.foldl (fun acc m => acc ++ msgContractBytes c m) Bytes.empty
```
hypotheses:
non-vacuity: plan.slots with [.g1] and the q_eval block swapped gives a different repack order; repackedProofLayout_arithmetic_ok-style KAT with distinct counts distinguishes it.

### repackProof / decodeWire  (def; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
/-- Port of VerifierBuildInputs::repack_proof (calldata.rs:43-128), over the codec. The
    Rust's identity/affine branch equals `c.toEip` under G1CodecLaws (eipShape, toEip_one);
    P-12 owes the equality with its faithful port. -/
def repackSlot {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (π : Bytes) :
    WireSlot → Nat → Except RepackError (Bytes × Nat)
  | .g1, cur =>
    match bytesTake π cur g1CompressedWidth with
    | none => .error (.invalidCompressedG1 cur "")           -- unreachable after the length check
    | some comp =>
      match c.ofCompressed? comp with
      | none => .error (.invalidCompressedG1 cur (hexOf comp))
      | some Q => .ok (c.toEip Q, cur + g1CompressedWidth)
  | .fr, cur =>
    match bytesTake π cur 32 with
    | none => .error (.nonCanonicalScalar cur "")
    | some le =>
      match frOfRepr? (p := p) le with
      | none => .error (.nonCanonicalScalar cur (hexOf (reverseBytes le)))
      | some s => .ok (frToInputBE s, cur + 32)

def repackProof {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) : Except RepackError Bytes := do
  if π.size ≠ plan.compressedLen then
    throw (.lengthMismatch plan.compressedLen π.size plan.prefixG1Count plan.numEvals plan.numPointSets)
  let (out, _) ← plan.slots.foldlM
    (fun (st : Bytes × Nat) sl => do
      let (b, cur') ← repackSlot (p := p) c π sl st.2
      pure (st.1 ++ b, cur'))
    (Bytes.empty, 0)
  pure out

/-- Pure schedule-driven decode of the compressed stream (the message-level mirror of
    repackProof); NOT decodeRust, which also runs the pipeline. -/
def decodeWire {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π : Bytes) : Option (List (Msg (Fr p) G₁)) := …  -- same walk, Msg.g1 / Msg.fr
```
hypotheses:
- hexOf : Bytes → String - any renderer; only constructor equality is ever stated
non-vacuity: repackedProofLayout_widthsDiffer_ok: swapping 48/128 in compressedLen rejects every real proof.

### encodeCalldataRaw / encodeCalldata / calldataOf  (def; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
/-- evm.rs:15 FN_SIG_VERIFY_PROOF. -/
def fnSigVerifyProof : Bytes := Midfall.Generator.bytesFromNats [0x1e, 0x8e, 0x1e, 0x13]

/-- evm.rs:22-38 encode_calldata: selector ‖ BE32(0x40) ‖ BE32(0x60 + len) ‖ BE32(len) ‖ proof ‖
    BE32(n) ‖ instances (fe_to_u256 = frWord, LE repr read as a word). Never pads: alignment
    comes from repackedLen_mod32. -/
def encodeCalldataRaw (proof : Bytes) (instances : List Word256) : Bytes :=
  fnSigVerifyProof ++ natToBytesBE 0x40 32 ++ natToBytesBE (0x40 + 0x20 + proof.size) 32 ++
    natToBytesBE proof.size 32 ++ proof ++ natToBytesBE instances.length 32 ++
    instances.foldl (fun acc w => acc ++ wordToBytesBE w) Bytes.empty

/-- calldata.rs:132-149 encode_calldata, with its instance-length check against
    GeneratorConfig.numInstances and the RepackError lift (Api.lean:388). -/
def encodeCalldata {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (numInstances : Nat)
    (plan : RepackedProofLayoutPlan) (c : G1Codec G₁) (π : Bytes) (inst : Array (Fr p)) :
    Except Midfall.Generator.GeneratorError Bytes := do
  if inst.size ≠ numInstances then
    throw (.planning "calldata"
      ("instance length mismatch: expected " ++ toString numInstances ++ ", got " ++ toString inst.size))
  match repackProof (p := p) plan c π with
  | .error e => throw (Midfall.Generator.GeneratorError.fromRepackError e)
  | .ok proof => pure (encodeCalldataRaw proof (inst.toList.map frWord))

/-- PLAN 9.5 calldataOf: the canonical calldata of (ms, raw instance words). -/
def calldataOf {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁)
    (ms : List (Msg (Fr p) G₁)) (inst : List Word256) : Bytes :=
  encodeCalldataRaw (encodeContractProof c ms) inst
```
hypotheses:
non-vacuity: poseidon dump cross-check: 4484 bytes, proof_len 0x10e0, instances head word 0x1140, n = 1 (survey (2)); a KAT on those numbers pins the three head words.

### decodeCalldata (ours, raw Word256, mirrors the contract's acceptance checks)  (def; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
/-- calldataload semantics: 32 bytes at `i`, zero past the end. -/
def cdWord (cd : Bytes) (i : Nat) : Word256 :=
  BitVec.ofNat 256 ((List.range 32).foldl (fun acc j => acc * 256 + ((cd.get? (i + j)).map UInt8.toNat).getD 0) 0)

/-- common_uncompressed_g1's range checks (AssemblyHelpers.yul:94-104). -/
def g1WordsOk (cd : Bytes) (cptr : Nat) : Bool :=
  let xh := (cdWord cd cptr).toNat; let xl := (cdWord cd (cptr + 32)).toNat
  let yh := (cdWord cd (cptr + 64)).toNat; let yl := (cdWord cd (cptr + 96)).toNat
  xh < 2 ^ 128 && yh < 2 ^ 128 &&
    xh * 2 ^ 256 + xl < Midfall.Assumptions.pBase && yh * 2 ^ 256 + yl < Midfall.Assumptions.pBase

def decodeSlots {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (c : G1Codec G₁) (cd : Bytes) :
    List WireSlot → Nat → Option (List (Msg (Fr p) G₁) × Nat)
  | [], cur => some ([], cur)
  | .g1 :: rest, cur => do
    guard (g1WordsOk cd cur)
    let b ← bytesTake cd cur g1EipWidth
    let Q ← c.ofEip? b                       -- off-curve/off-subgroup bytes revert later via G1MSM/pairing (points_subgroup_checked)
    let (ms, cur') ← decodeSlots c cd rest (cur + g1EipWidth)
    pure (.g1 Q :: ms, cur')
  | .fr :: rest, cur => do
    let w := cdWord cd cur
    guard (w.toNat < p)                        -- TranscriptProofParser.yul:319, :382
    let (ms, cur') ← decodeSlots c cd rest (cur + 32)
    pure (.fr (Nat.cast w.toNat) :: ms, cur')

/-- PLAN 9.5 decodeCalldata. Every rejection is a template line (survey (1)); instances
    are returned RAW (R-26.7) and the modulus test is `< p`, with p = r pinned by the Surface. -/
def decodeCalldata {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (L : ProofCalldataLayout)
    (numInstances : Nat) (c : G1Codec G₁) (cd : Bytes) :
    Option (List (Msg (Fr p) G₁) × Array Word256) := do
  let plan := RepackedProofLayoutPlan.fromProofLayout L
  let numInstCptr := L.proofEnd
  let instCptr := numInstCptr + 32
  guard (bytesTake cd 0 4 == some fnSigVerifyProof)                                   -- solc dispatcher
  guard (L.proofCptr == Midfall.Generator.abiVerifyProofProofCptr)                    -- 0x64
  guard ((cdWord cd 4).toNat == 0x40 && (cdWord cd 0x24).toNat == numInstCptr - 4)    -- Halo2Verifier.sol:148
  guard ((cdWord cd 0x44).toNat == L.proofLen)                                         -- VkLoading.yul:101
  guard ((cdWord cd numInstCptr).toNat == numInstances)                                -- VkLoading.yul:102
  guard (cd.size == instCptr + 32 * numInstances)                                      -- VkLoading.yul:106-109
  let (ms, cur) ← decodeSlots (p := p) c cd plan.slots L.proofCptr
  guard (cur == numInstCptr)                                                           -- TranscriptProofParser.yul:416
  let inst := (List.range numInstances).map (fun i => cdWord cd (instCptr + 32 * i))
  guard (inst.all (fun w => w.toNat < p))                                              -- TranscriptProofParser.yul:63-68
  pure (ms, inst.toArray)
```
hypotheses:
- p = Midfall.Assumptions.r (Surface.modulusPinned) - the contract compares against the literal FR_MODULUS
- the decision to require c.ofEip? success models the later G1MSM/pairing rejection of non-points: sound only with points_subgroup_checked (every absorbed point reaches a precompile; G1ADD does not subgroup-check)
non-vacuity: dropping the exact-size guard accepts trailing bytes the contract rejects (VkLoading.yul:106-112), which falsifies calldata_canonical; dropping `< p` on instances accepts transcript aliases (TranscriptProofParser.yul:63).

### repackedLen_mod32 / proofLen_eq_repackedLen / sum_commitmentReadGroups  (lemma-provable-now; provable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
theorem repackedLen_mod32 (plan : RepackedProofLayoutPlan) : plan.repackedLen % 32 = 0 := by
  unfold RepackedProofLayoutPlan.repackedLen; omega  -- g1Bytes = 128, wordBytes = 32

theorem sum_commitmentReadGroups (L : ProofCalldataLayout) :
    (RepackedProofLayoutPlan.fromProofLayout L).prefixG1Count = L.commitmentG1Count := by sorry

/-- For layouts built by fromProtocol at 0x64 the proof length is the repacked length and
    the sections tile exactly (survey (5): VM and Direct plans share this layout). -/
theorem proofLen_eq_repackedLen (protocol : Midfall.Generator.ProtocolPlan) (numEvals numPointSets : Nat)
    (L : ProofCalldataLayout)
    (h : ProofCalldataLayout.fromProtocol protocol Midfall.Generator.abiVerifyProofProofCptr numEvals numPointSets = .ok L) :
    L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen ∧ L.proofEnd = L.proofCptr + L.proofLen := by sorry
```
hypotheses:
- h : fromProtocol succeeded - hand-built layouts can have inconsistent byteLen (ProofSection.new is never recomputed)
non-vacuity: commitmentReadGroups_disagreeWhenHandBuilt_ok shows a hand-built layout breaks the prefix count identity; the filter of zero counts in commitmentReadGroups is why the sum lemma is not rfl.

### calldata_roundtrip  (theorem-sorry; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
theorem calldata_roundtrip {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [Group G₁]
    (L : ProofCalldataLayout) (hL : L.proofCptr = Midfall.Generator.abiVerifyProofProofCptr)
    (hlen : L.proofLen = (RepackedProofLayoutPlan.fromProofLayout L).repackedLen)
    (hend : L.proofEnd = L.proofCptr + L.proofLen)
    (c : G1Codec G₁) (hc : Midfall.Assumptions.G1CodecLaws c)
    (ms : List (Msg (Fr p) G₁)) (hshape : ms.map Msg.slot = (RepackedProofLayoutPlan.fromProofLayout L).slots)
    (numInstances : Nat) (inst : List Word256) (hn : inst.length = numInstances)
    (hinst : ∀ w ∈ inst, w.toNat < p) :
    decodeCalldata (p := p) L numInstances c (calldataOf c ms inst) = some (ms, inst.toArray) := by
  sorry
```
hypotheses:
- hL/hlen/hend - from proofLen_eq_repackedLen on fromProtocol layouts (Surface.hProofLayout)
- hc.eipShape/toEip_one - each G1 message is 128 bytes passing g1WordsOk; hc.ofEip_toEip - the point is recovered
- hshape - the message list has the layout's shape (readScheduleAgrees for decodeRust outputs)
- hinst - instance words canonical (frWord of Fr p with p < 2^256 gives this)
non-vacuity: a decoder that reads the instance count at INSTANCE_CPTR instead of NUM_INSTANCE_CPTR fails for n ≥ 1; an encoder emitting LE scalars (R-20 class) fails the `< p`-then-cast equality for s = 1.

### calldata_canonical (EXACT, both modes)  (theorem-sorry; statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
/-- Exact, with no ≈: trailing bytes and non-canonical words fail closed, G1 bytes are
    canonical by eipRoundtrip, and instances are returned raw. The R-25 malleability lives
    in decodeAcc (seen through accWords), not in the calldata, so this holds in
    accumulator mode too. -/
theorem calldata_canonical {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (L : ProofCalldataLayout) (numInstances : Nat) (c : G1Codec G₁) (hc : c.eipRoundtrip)
    (cd : Bytes) (ms : List (Msg (Fr p) G₁)) (inst : Array Word256)
    (h : decodeCalldata (p := p) L numInstances c cd = some (ms, inst)) :
    cd = calldataOf c ms inst.toList := by sorry
```
hypotheses:
- hc : eipRoundtrip (decoder-first) - accepted 128-byte strings re-encode to themselves; this is exactly the law Codec.lean:92-107 was restated for
non-vacuity: two 128-byte strings decoding to one point (a codec without eipRoundtrip) give two calldatas for one (ms, inst), refuting the equation.

### repack_spec (split form; PLAN iff is false)  (theorem-sorry; FALSE-as-planned (counterexample: byte-valid proof with a pipeline panic); split form statable-now; M5) — formal/Midfall/Lowering/Calldata.lean
```lean
/-- Wire-level iff: repackProof succeeds exactly when the compressed stream decodes by the
    schedule, and the output is the contract bytes of those messages. -/
theorem repack_spec_wire {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (plan : RepackedProofLayoutPlan)
    (c : G1Codec G₁) (π π' : Bytes) :
    repackProof (p := p) plan c π = .ok π' ↔
      ∃ ms, decodeWire (p := p) plan c π = some ms ∧ π' = encodeContractProof c ms := by sorry

/-- The pipeline-level half the PLAN wanted, in the only direction that is true. -/
theorem repack_spec_of_decodeRust (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) (π : Bytes) (plan : RepackedProofLayoutPlan)
    (hc : E.g1.compressedRoundtrip)
    (hsched : ∀ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms → ms.map Msg.slot = plan.slots)
    (ms : List (Msg (Fr p) G₁)) (hdec : decodeRust (Gₜ := Gₜ) E F vk inst π = some ms) :
    repackProof (p := p) plan E.g1 π = .ok (encodeContractProof E.g1 ms) := by sorry
```
hypotheses:
- hc : compressedRoundtrip - the log records are the consumed 48-byte slices; decoder-first gives re-serialisation equality (same lemma the provable verifyNative_iff_msgs needs)
- hsched - Exec read-schedule shape = plan.slots (Obligations.readScheduleAgrees; a Protocol ↔ Exec bridge)
- also needed: the transcript-log-concatenates-to-the-consumed-prefix lemma (Transcript.read appends (width, repr) and advances pos)
non-vacuity: PLAN's `repackProof = .ok π' ↔ ∃ ms, decodeRust … = some ms ∧ …` is FALSE: a proof whose bytes all decode but whose pipeline panics (x3 ∈ pointSets, kzg/mod.rs:479, R-35; or logup.rs:460) repacks fine while decodeRust = none.

### qvmFrModulus_eq_r / qvmToFr homomorphism  (lemma-provable-now; provable-now; M6) — formal/Midfall/Lowering/Qvm.lean
```lean
open Midfall.Generator in
theorem qvmFrModulus_eq_r : qvmFrModulus = Midfall.Assumptions.r := by decide  -- two Nat literals (fallback: rfl)

abbrev FrR := Fr Midfall.Assumptions.r

def qvmToFr (v : Midfall.Generator.QVMFr) : FrR := (v : FrR)

theorem qvmToFr_add (a b) : qvmToFr (Midfall.Generator.qvmFrAdd a b) = qvmToFr a + qvmToFr b := by
  unfold qvmToFr Midfall.Generator.qvmFrAdd; rw [qvmFrModulus_eq_r, ZMod.natCast_mod, Nat.cast_add]
theorem qvmToFr_mul (a b) : qvmToFr (Midfall.Generator.qvmFrMul a b) = qvmToFr a * qvmToFr b := by sorry
theorem qvmToFr_neg (a) (ha : a < Midfall.Generator.qvmFrModulus) : qvmToFr (Midfall.Generator.qvmFrNeg a) = - qvmToFr a := by sorry
theorem qvmToFr_injOn (a b) (ha : a < qvmFrModulus) (hb : b < qvmFrModulus) (h : qvmToFr a = qvmToFr b) : a = b := by sorry
```
hypotheses:
- ha/hb canonicity for neg/injectivity - QVMFr is Nat, only canonical representatives are field elements
non-vacuity: replaces the Bool KAT qvmFrModulus_agreesWithBlsR_ok by a kernel fact; a wrong literal digit makes `decide` fail.

### Valuation / evalExprρ / memKey / memOfρ / NoMiss / CacheConsistent / evalQuotientExpr_memOfρ  (def; provable-now; M6) — formal/Midfall/Lowering/Qvm.lean
```lean
open Midfall.Generator (QVMFr QVMFault QuotientExpr QuotientMem QuotientRefMemory fqFromU256 qvmFrAdd qvmFrMul qvmFrNeg)

/-- A valuation of verifier memory: domain 0 = literal pointers, domain 1+t = token t
    (VmReference.lean:433-457); keys wrap exactly like the cache key (domain % 256,
    address % 2^32), which is what makes token 0xff land in the literal domain
    (KAT tokenDomainU8Wrap_releaseProfile_ok). -/
abbrev Valuation := Nat → Nat → QVMFr

def memKey : QuotientMem → Nat × Nat
  | .literal ptr => (0, ptr % 2 ^ 32)
  | .token t => ((1 + t) % 256, 0)
  | .tokenOffset t o => ((1 + t) % 256, o % 2 ^ 32)

/-- The shadow denotation of an expression under a valuation. -/
def evalExprρ (ρ : Valuation) : QuotientExpr → Except QVMFault QVMFr
  | .const v => fqFromU256 v
  | .mem m => .ok (ρ (memKey m).1 (memKey m).2)
  | .add l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrAdd a b)
  | .mul l r => do let a ← evalExprρ ρ l; let b ← evalExprρ ρ r; pure (qvmFrMul a b)
  | .neg e => do let a ← evalExprρ ρ e; pure (qvmFrNeg a)

/-- A reference memory whose cache is pre-populated from ρ on the keys S: the ported
    interpreter then reads ρ (cache hits, VmReference.lean:433-438) without deriving.
    This gives the ∀ρ statements WITHOUT touching VmReference.lean. -/
def memOfρ (ρ : Valuation) (S : List (Nat × Nat)) : QuotientRefMemory :=
  { seed := Bytes.empty,
    cache := S.map (fun k => (k.1 % 256, k.2 % 2 ^ 32, ρ (k.1 % 256) (k.2 % 2 ^ 32))) }

/-- No miss happened: every read was a cache hit (the memo table did not grow). -/
def NoMiss (m m' : QuotientRefMemory) : Prop := m'.cache = m.cache

/-- The invariant certifier memories satisfy (fresh memories trivially). -/
def CacheConsistent (m : QuotientRefMemory) : Prop :=
  ∀ e ∈ m.cache, e.2.2 = Midfall.Generator.deriveReferenceMemory m.seed e.1 e.2.1 ∧ e.1 < 256 ∧ e.2.1 < 2 ^ 32

def leafKeys (e : QuotientExpr) : List (Nat × Nat) := e.memLeaves.map memKey

theorem evalQuotientExpr_memOfρ (ρ : Valuation) (e : QuotientExpr) (S : List (Nat × Nat))
    (hS : ∀ k ∈ leafKeys e, k ∈ S) :
    Midfall.Generator.evalQuotientExpr e (memOfρ ρ S) = (evalExprρ ρ e).map (fun v => (v, memOfρ ρ S)) := by sorry
```
hypotheses:
- hS - leaves must be cached, else derive fires and the value is a keccak output, not ρ
non-vacuity: a memKey without the % 256 wrap disagrees with the interpreter on token 0xff (the existing KAT); evalQuotientExpr_memOfρ fails if S misses one leaf.

### denoteLimbShape / denoteModarith7 / RecognizersSound / noShapeRecognizers_sound  (structure; statable-now (noShapeRecognizers_sound provable-now); M6) — formal/Midfall/Lowering/Qvm.lean
```lean
open Midfall.Generator (QuotientLimbShape QuotientModarith7Shape QuotientShapeRecognizers noShapeRecognizers)

def denoteLin (ρ : Valuation) (terms : List (Word256 × Nat)) : Except QVMFault QVMFr :=
  terms.foldlM (fun acc t => do let c ← fqFromU256 t.1; pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) 0

/-- Value of a recognised limb shape under ρ, following the byte decoders limbLinearForm /
    limbRowForm / limbPairwiseForm (VmReference.lean:577-634): row = mload(lhs) · Σ cᵢ·mload(rhsᵢ),
    pairwise = Σ_{i,j<7} coeff[i+j] · mload(a+32i) · mload(b+32j). -/
def denoteLimbShape (ρ : Valuation) : QuotientLimbShape → Except QVMFault QVMFr
  | .lin7 terms => denoteLin ρ terms
  | .bilin7Row lhs terms => do let inner ← denoteLin ρ terms; pure (qvmFrMul (ρ 0 (lhs % 2 ^ 32)) inner)
  | .bilin7Pairwise a b coeffs =>
    (List.range 7).foldlM (fun acc i => (List.range 7).foldlM (fun acc j => do
        let c ← fqFromU256 (coeffs.getD (i + j) 0)
        pure (qvmFrAdd acc (qvmFrMul (qvmFrMul (ρ 0 ((a + 32 * i) % 2 ^ 32)) (ρ 0 ((b + 32 * j) % 2 ^ 32))) c))) acc) 0

/-- modarith7Form (VmReference.lean:636-700): const + Σ lin + Σ rows + Σ pairwise + Σ c·mem +
    Σ c·l·r, the whole sum multiplied by mload(cond) when present. A zero `constant` is
    the absent FLAG_CONST (contributes 0 either way). -/
def denoteModarith7 (ρ : Valuation) (sh : QuotientModarith7Shape) : Except QVMFault QVMFr := do
  let v0 ← fqFromU256 sh.constant
  let v1 ← sh.lin.foldlM (fun acc t => do pure (qvmFrAdd acc (← denoteLin ρ t))) v0
  let v2 ← sh.rows.foldlM (fun acc r => do pure (qvmFrAdd acc (← denoteLimbShape ρ (.bilin7Row r.1 r.2)))) v1
  let v3 ← sh.pairwise.foldlM (fun acc q => do pure (qvmFrAdd acc (← denoteLimbShape ρ (.bilin7Pairwise q.1 q.2.1 q.2.2)))) v2
  let v4 ← sh.memTerms.foldlM (fun acc t => do let c ← fqFromU256 t.1; pure (qvmFrAdd acc (qvmFrMul c (ρ 0 (t.2 % 2 ^ 32))))) v3
  let v5 ← sh.productTerms.foldlM (fun acc t => do let c ← fqFromU256 t.1; pure (qvmFrAdd acc (qvmFrMul (qvmFrMul c (ρ 0 (t.2.1 % 2 ^ 32))) (ρ 0 (t.2.2 % 2 ^ 32))))) v4
  pure (match sh.cond with | none => v5 | some ptr => qvmFrMul v5 (ρ 0 (ptr % 2 ^ 32)))

def shapePtrsU16 : QuotientLimbShape → Prop := …   -- every pointer ≤ 0xffff (emitU16 exactness)
def modarith7WellFormed (sh : QuotientModarith7Shape) : Prop := …  -- 7 terms per lin/row, 13 coeffs, counts ≤ 255, pointers ≤ 0xffff

/-- Soundness of the recognizer hooks (P-09f is unported): a recognised shape denotes the
    expression under EVERY valuation. Compile correctness is false for arbitrary hooks. -/
structure RecognizersSound (r : QuotientShapeRecognizers) : Prop where
  pow5 : ∀ e b, r.pow5Base e = some b → ∀ ρ,
    evalExprρ ρ e = (evalExprρ ρ b).map (fun v => qvmFrMul v (qvmFrMul (qvmFrMul v v) (qvmFrMul v v)))
  limb : ∀ e sh, r.limbShape e = some sh →
    sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ, evalExprρ ρ e = denoteLimbShape ρ sh
  limbSub : ∀ e sh res matched, r.limbSubshape e = some (sh, res, matched) →
    matched ≠ [] ∧ sh.wellFormed = true ∧ shapePtrsU16 sh ∧ ∀ ρ,
      evalExprρ ρ e = (do let a ← denoteLimbShape ρ sh; let b ← evalExprρ ρ res; pure (qvmFrAdd a b)) ∧
      denoteLimbShape ρ sh = matched.foldlM (fun acc m => do pure (qvmFrAdd acc (← evalExprρ ρ m))) 0
  modarith7 : ∀ e sh, r.modarith7Shape e = some sh →
    modarith7WellFormed sh ∧ ∀ ρ, evalExprρ ρ e = denoteModarith7 ρ sh

theorem noShapeRecognizers_sound : RecognizersSound noShapeRecognizers := by
  constructor <;> intros <;> simp_all [noShapeRecognizers]
```
hypotheses:
- matched ≠ [] - KAT emptyMatchedHookIsAFrontier_ok shows an empty match breaks the stack accounting
- wellFormed/shapePtrsU16 - emitLimbShape does not re-check arity (VmTypes.lean:511) and emitU16 truncates
non-vacuity: a pow5Base hook returning `some e` for every e is unsound (e ≠ e^5); noShapeRecognizers_sound is the vacuous baseline the dual-build certifier compares against.

### exprBounded / qvm_compile_correct_identity (form b)  (theorem-sorry; statable-now; M6) — formal/Midfall/Lowering/Qvm.lean
```lean
/-- Operand widths the builder encodes exactly: tokens < 256, pointers and offsets < 2^32
    (pushByte pushes raw Nats, emitU32 truncates - VmBuilder.lean:348). -/
def exprBounded : QuotientExpr → Prop
  | .const _ => True
  | .mem (.literal ptr) => ptr < 2 ^ 32
  | .mem (.token t) => t < 256
  | .mem (.tokenOffset t o) => t < 256 ∧ o < 2 ^ 32
  | .add l r | .mul l r => exprBounded l ∧ exprBounded r
  | .neg e => exprBounded e

/-- Per-identity compile correctness, ∀ρ (strictly stronger than the certifier's single
    Schwartz-Zippel sample, VmCertify.lean:31-48): the bytes `identityExpr` appended, compacted
    and stripped of their fold, evaluate under the pre-populated memory to the expression's
    denotation, reading only the expression's leaves (no miss). -/
theorem qvm_compile_correct_identity (r : QuotientShapeRecognizers) (hr : RecognizersSound r)
    (s₀ s₁ : Midfall.Generator.QuotientBuilder.QuotientProgramBuilder) (e : QuotientExpr)
    (t : Midfall.Generator.QuotientTarget) (gap : Option Nat) (hb : exprBounded e)
    (hemit : Midfall.Generator.QuotientBuilder.identityExpr r s₀ e t gap = .ok s₁)
    (hconsts : ∀ c ∈ s₁.consts, c.toNat < Midfall.Generator.qvmFrModulus)
    (cseg seg : List Nat)
    (hcompact : Midfall.Generator.QuotientBuilder.compactQuotientRuns (s₁.bytes.drop s₀.bytes.length) = .ok cseg)
    (hseg : Midfall.Generator.QuotientBuilder.finalizedIdentitySegment cseg = some seg)
    (ρ : Valuation) :
    ∃ v, Midfall.Generator.evalQuotientIdentity seg s₁.consts (memOfρ ρ (leafKeys e)) =
           .ok (v, memOfρ ρ (leafKeys e)) ∧
         evalExprρ ρ e = .ok v := by sorry
```
hypotheses:
- hr - compile correctness is false for arbitrary hooks (survey)
- hb - without it a token ≥ 256 is truncated by qvmBytesOfNats at finish and reads a different domain
- hemit = .ok - about 40 builder panic sites (>65536 constants, u16/u24 overflow, selector > 255, gap > 0xffff, stack leak)
- hconsts - Yul PUSH_CONST is a raw mload; fqFromU256 panics at ≥ r on both the VM and the expression side, so the ∃ v form needs canonical constants
- hcompact/hseg - compaction runs in finish over the whole stream; segments are the compactions of raw segments because runs cannot straddle a fold byte (owed lemma)
non-vacuity: a builder emitting rhs before lhs for `sub`-like trees is caught only by a non-commutative test; here NEG is unary so the witness is `tryEmitAddProduct` with swapped operands under a ρ with ρ 0 a ≠ ρ 0 b (certify KATs use distinct values).

### buildItems / buildPlan / qvm_compile_correct_certifier / qvm_compile_correct_program (form a)  (theorem-sorry; statable-now; M6) — formal/Midfall/Lowering/Qvm.lean
```lean
open Midfall.Generator (QuotientProgramItem QuotientProgramPlan QuotientProgramBuild SelectorFoldPlan)
open Midfall.Generator.QuotientBuilder (QuotientProgramBuilder M identityExpr nativePermutation nativeLookup nativeIdentity finish withLimbVmOps)

/-- The plan-items driver (quotient.rs:2120 build_quotient_program_items_with_limb_ops is
    unported); mirrors QuotientCertifyKats.buildStream but threads `r` and the plan's gaps. -/
def buildItems (r : QuotientShapeRecognizers) (sf : SelectorFoldPlan) :
    List QuotientProgramItem → QuotientProgramBuilder → M QuotientProgramBuilder
  | [], s => .ok s
  | .identity id :: rest, s => do buildItems r sf rest (← identityExpr r s id.expr id.target (sf.gapFor id))
  | .nativePermutation :: rest, s => do buildItems r sf rest (← nativePermutation s)
  | .nativeLookup :: rest, s => do buildItems r sf rest (← nativeLookup s)
  | .nativeIdentity i :: rest, s => do buildItems r sf rest (← nativeIdentity s i)

def buildPlan (r : QuotientShapeRecognizers) (plan : QuotientProgramPlan) (s₀ : QuotientProgramBuilder) :
    M QuotientProgramBuild :=
  buildItems r plan.selectorFold plan.items s₀ >>= finish

/-- Form (a): the certifier walk succeeds on every consistent memory and consumes the whole
    stream, hence `certifyQuotientProgram` succeeds for every VK payload. -/
theorem qvm_compile_correct_certifier (r) (hr : RecognizersSound r) (plan : QuotientProgramPlan)
    (limbOps : Bool) (build : QuotientProgramBuild)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build)
    (hbounded : ∀ id, QuotientProgramItem.identity id ∈ plan.items → exprBounded id.expr)
    (hconsts : ∀ c ∈ build.consts, c.toNat < Midfall.Generator.qvmFrModulus)
    (mem : QuotientRefMemory) (hcc : CacheConsistent mem) :
    ∃ mem', Midfall.Generator.QuotientCertify.certifyItemWalk plan build (Midfall.Generator.qvmBytesToNats build.bytes) mem =
      .ok ((Midfall.Generator.qvmBytesToNats build.bytes).length, mem') := by sorry

theorem qvm_compile_correct_program (… same …) (vk : Midfall.Generator.Halo2VerifyingKey) :
    Midfall.Generator.QuotientCertify.certifyQuotientProgram plan build vk = .ok () := by sorry
```
hypotheses:
- hbuild = .ok - the builder's panic sites (gap none for a selector, idx > 255, gap > 0xffff, stack leak)
- hcc - the walk threads one memory through VM and oracle (VmCertify.lean:499-560); consistency is what lets both sides observe ρ := deriveReferenceMemory seed
- values only are compared (Prod.fst); the returned memories are never equated
non-vacuity: certify KATs (threeIdentityBuild) exercise a selector gap; a driver that passed `none` as the gap panics at siteNoSelectorGap, so hbuild cannot hold; a wrong plan.items order makes checkFold's positional check fail.

### builder_segments_total (qvm_validated_noOOB, builder form) + Obligations fields (validator form)  (theorem-sorry; builder form statable-now; validator form needs P-09e; M6 (builder form); validator form blocked on P-09e) — formal/Midfall/Lowering/Qvm.lean (theorem) and Obligations.lean (fields)
```lean
/-- D-P20 item 2 restated over the two real fault classes: segments of a builder-produced
    program never fault at all (so in particular never .readPastEnd / .constSlotOutOfRange),
    on every memory, when the constants are canonical. -/
theorem builder_segments_total (r) (hr : RecognizersSound r) (plan) (limbOps) (build)
    (hbuild : buildPlan r plan (withLimbVmOps limbOps) = .ok build) (hbounded) (hconsts)
    (cursor exprEnd foldOp : Nat)
    (hstart : cursor ∈ itemStarts plan build)   -- the cursors certifyItemWalk visits (definable from quotientOpLen)
    (hseg : Midfall.Generator.QuotientCertify.identitySegment (Midfall.Generator.qvmBytesToNats build.bytes) cursor = .ok (exprEnd, foldOp))
    (mem : QuotientRefMemory) :
    ∃ v mem', Midfall.Generator.evalQuotientIdentity
      (((Midfall.Generator.qvmBytesToNats build.bytes).drop cursor).take (exprEnd - cursor)) build.consts mem = .ok (v, mem') := by sorry

/- Obligations fields (validator abstract until P-09e lands; no theorem line):
  validate : List Nat → List Word256 → OperandModel → Except String Unit
  qvm_validated_noBoundsFault : ∀ bytes consts model, validate bytes consts model = .ok () →
    ∀ seg ∈ segmentsOf bytes, ∀ mem f, evalQuotientIdentity seg consts mem = .error f →
      (match f with | .readPastEnd _ => False | .constSlotOutOfRange _ _ => False | _ => True)
  qvm_validated_windows : ∀ bytes consts model, validate … = .ok () →
    ∀ k ∈ operandKeys bytes, k ∈ model.readWindows   -- vk_payload, user_challenges, theta..instance_eval+0x20, decoded_proof_evals (plan.rs:570-618) -/
```
hypotheses:
- the PLAN's `.oob` does not exist (QVMFault has readPastEnd/constSlotOutOfRange only, VmReference.lean:284); certifier memory is a PRNG over u32 so no address can be out of range
- the memory-window bound is a Yul/EVM-layer statement and stays abstract (P-09e: QuotientReadModel/OperandModel unported)
non-vacuity: a hand-built program [qOpPushConst, 0xff, 0xff] faults .constSlotOutOfRange on an empty table, so totality is not automatic; the builder-form theorem excludes it only through hbuild.

### globalIdentities / quotientFold / SelectorFoldConsistent / IdentityCorrespondence  (def; statable-now; M6) — formal/Midfall/Lowering/QvmFold.lean
```lean
open Midfall.Generator (QuotientIdentity QuotientProgramItem QuotientProgramPlan SelectorFoldPlan QVMFr qvmFrAdd qvmFrMul qvmFrNeg qvmFrModulus)

/-- The global y-order: inline prefix, items with native markers expanded, structured tail
    (QuotientNumeratorBlock.yul:198, :1205-1279, :1368; R-16/R-19). -/
def expandItem (plan : QuotientProgramPlan) : QuotientProgramItem → List QuotientIdentity
  | .identity id => [id]
  | .nativePermutation => plan.nativePermutationIdentities
  | .nativeLookup => plan.nativeLookupIdentities
  | .nativeIdentity i => (plan.nativeIdentities[i]?).toList

def globalIdentities (plan : QuotientProgramPlan) : List QuotientIdentity :=
  plan.inlineIdentities ++ plan.items.flatMap (expandItem plan) ++ plan.structuredTailIdentities

def qvmFrPow (y : QVMFr) : Nat → QVMFr
  | 0 => 1 % qvmFrModulus
  | n + 1 => qvmFrMul (qvmFrPow y n) y

structure FoldState where
  qn : QVMFr
  buckets : List QVMFr   -- indexed by position in plan.sortedSimple

/-- FOLD_MAIN (yul:1284-1299): qn := qn·y + v. FOLD_SELECTOR (yul:1303-1341): qn := qn·y and
    bucket[s] := bucket[s]·y^gap (only if gap ≠ 0) + v. -/
def foldStep (y : QVMFr) (sf : SelectorFoldPlan) (st : FoldState) (id : QuotientIdentity) (v : QVMFr) : FoldState :=
  match id.target with
  | .main => { st with qn := qvmFrAdd (qvmFrMul st.qn y) v }
  | .selector s =>
    let gap := (sf.gapFor id).getD 0
    { qn := qvmFrMul st.qn y,
      buckets := st.buckets.modify (fun b => qvmFrAdd (if gap = 0 then b else qvmFrMul b (qvmFrPow y gap)) v) s }

/-- The whole-stream fold (NEW definition, D-P20 addendum): per-identity values in global
    order ⇒ (QUOTIENT_EVAL = -qn, selector buckets after their tails, yul:1382-1394). -/
def quotientFold (plan : QuotientProgramPlan) (y : QVMFr) (vals : List QVMFr) : QVMFr × List QVMFr :=
  let init : FoldState := { qn := 0, buckets := List.replicate plan.sortedSimple.length 0 }
  let st := (List.zip (globalIdentities plan) vals).foldl (fun st iv => foldStep y plan.selectorFold st iv.1 iv.2) init
  (qvmFrNeg st.qn, List.zipWith (fun b t => qvmFrMul b (qvmFrPow y t)) st.buckets plan.selectorFold.tailExponents)

/-- What quotient_program_plan / selector_fold_plan (quotient.rs:356/426, P-10) guarantee. -/
def SelectorFoldConsistent (plan : QuotientProgramPlan) : Prop :=
  let ids := globalIdentities plan
  plan.sortedSimple.Sorted (· < ·) ∧
  (∀ i (h : i < ids.length), ids[i].meta_.globalIndex = i) ∧
  (∀ i (h : i < ids.length) s, ids[i].target = .selector s → s < plan.sortedSimple.length ∧
     ∀ j (hj : j < i), ids[j].target = .selector s →
       (∀ k, j < k → k < i → ∀ hk, ids[k]'hk |>.target ≠ .selector s) →
       plan.selectorFold.gapFor ids[i] = some (i - j)) ∧
  plan.selectorFold.tailExponents.length = plan.sortedSimple.length ∧
  (∀ s (hs : s < plan.sortedSimple.length), (∃ i (h : i < ids.length), ids[i].target = .selector s) ∧
     ∀ i (h : i < ids.length), ids[i].target = .selector s →
       (∀ k, i < k → ∀ hk, ids[k]'hk |>.target ≠ .selector s) →
       plan.selectorFold.tailExponents[s] = ids.length - 1 - i)

/-- The bridge between the QVM identity list and the Lean verifier's tagged expression array
    (partiallyEvaluateIdentities output): same length, same values, bucket s ↔ fixed column
    plan.sortedSimple[s] (quotient_expr_from_expression, QVM:2870, is unported). -/
def IdentityCorrespondence (plan : QuotientProgramPlan) (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) : Prop :=
  let ids := globalIdentities plan
  exprs.size = ids.length ∧ vals.length = ids.length ∧
  ∀ i (h : i < ids.length), (exprs[i]'(by omega)).2 = qvmToFr (vals[i]'(by omega)) ∧
    (match ids[i].target with
     | .main => (exprs[i]'(by omega)).1 = none
     | .selector s => (exprs[i]'(by omega)).1 = plan.sortedSimple[s]?)
```
hypotheses:
non-vacuity: foldStep without the `qn := qn·y` on the selector arm breaks the y-alignment of later main identities (the Yul comment at yul:1312-1315 exists for this); globalIdentities with items before inlineIdentities changes every y power.

### quotientFold_matches_linearization  (theorem-sorry; statable-now; M6) — formal/Midfall/Lowering/QvmFold.lean
```lean
/-- The fold equals computeLinearizationCommitment's reverse y-fold (Linearization.lean:68-110):
    identity i gets y^(m-1-i); the None bucket is subtracted into the eval; Some buckets
    appear in ascending column order, which is ascending s because sortedSimple is sorted. -/
theorem quotientFold_matches_linearization {G₁ : Type} (plan : QuotientProgramPlan)
    (hcons : SelectorFoldConsistent plan)
    (exprs : Array (Option Nat × FrR)) (vals : List QVMFr) (hvals : ∀ v ∈ vals, v < qvmFrModulus)
    (hcorr : IdentityCorrespondence plan exprs vals)
    (vk : VerifyingKey FrR G₁) (x y xn sf : FrR) (limbs : Array G₁) (q : VerifierQuery FrR G₁)
    (hq : computeLinearizationCommitment exprs vk x y xn sf limbs = .ok q) :
    let r := quotientFold plan y.val vals
    q.eval = qvmToFr r.1 ∧
    ∃ pts labs, q.commitment = .linear pts
      ((limbScalars limbs.size xn sf) ++ r.2.map qvmToFr).toArray labs := by sorry
  -- limbScalars n xn sf := the n scalars (1 - xn)·sf^i, extracted from Linearization.lean:84-90
```
hypotheses:
- hcons - gaps/tails must encode positions; a gap off by one moves a bucket by y (R-16 class)
- hcorr - the bucket key translation (FOLD_SELECTOR u8 = position in sortedSimple vs Lean key = selector index): whether Selector.index equals the fixed-column index used at linearization/verifier.rs:84 is a Rust-side invariant to pin, not assumed here
- hvals - canonical values, so qvmToFr is a homomorphism
- every s in sortedSimple is targeted (in hcons) - otherwise an empty bucket (0) has no counterpart in q's scalars
non-vacuity: a one-identity circuit cannot see the error (R-19); the KAT must have ≥ 2 main and ≥ 2 selector identities in interleaved order (R-30 rule: every collapsed dimension ≥ 2).

### EvaluatorFrame / FrameWellFormed / frameValuation / qvm_yul_refines (Obligations field)  (obligation-field; needs P-09h/P-13 + Midfall.Yul.Bridge; M6 statement; proof blocked on P-09h, P-13 (QuotientNumeratorBlock AST) and Bridge) — formal/Midfall/Lowering/Surface.lean + Obligations.lean
```lean
/-- The evaluator's calldata = memory[vk_mptr, vk_mptr + frame_len) (quotient.rs:760-794;
    Halo2QuotientEvaluator.sol:110-118 reverts iff calldatasize ≠ QUOTIENT_FRAME_LEN). -/
structure EvaluatorFrame where
  base : Nat
  len : Nat
  mem : Nat → UInt8

def EvaluatorFrame.bytes (f : EvaluatorFrame) : List UInt8 := (List.range f.len).map (fun i => f.mem (f.base + i))
def EvaluatorFrame.word (f : EvaluatorFrame) (a : Nat) : Word256 := …  -- 32 BE bytes of f.mem at a

/-- Token bases (QuotientNumeratorBlock.yul:471-479, :538-566): 1 ↦ l0Mptr, 2 ↦ lLastMptr,
    3 ↦ lBlindMptr, 4 ↦ betaMptr, 5 ↦ gammaMptr, 6 ↦ xMptr, 7 ↦ thetaMptr,
    8 ↦ trashChallengeMptr, 9 ↦ instanceEvalMptr (Ptr → byte via Value.asUsizeNat). -/
def tokenBase (lay : Midfall.Generator.VerifierMemoryLayout) : Nat → Nat := …

def frameValuation (lay) (f : EvaluatorFrame) : Valuation := fun d a =>
  if d = 0 then (f.word a).toNat else (f.word (tokenBase lay d + a)).toNat

/-- THE FRAME CONTAINS THE PROGRAM (const table at vk_mptr + quotient_const_offset_words,
    bytecode at vk_mptr + quotient_program_offset_words, quotient.rs:189-217): the VK window
    must be pinned to the lowered payload or the statement is false for adversarial calldata. -/
def FrameWellFormed (S : Surface …) (f : EvaluatorFrame) : Prop :=
  f.base = Midfall.Generator.Value.asUsizeNat (Midfall.Generator.ptrValue S.plan.vkMptr) ∧
  f.len = S.qext.frameLen ∧
  (∀ i < S.plan.hvk.len, f.mem (f.base + i) = S.plan.hvk.bytes.get! i) ∧
  (∀ k ∈ readKeys S.plan.qbuild, (frameValuation S.plan.memory f k.1 k.2) < qvmFrModulus)  -- PUSH_MEM is a raw mload

/- Obligations field (needs Bridge.Run and the evaluator runtime object; blocked on P-09h/P-13):
  qvm_yul_refines : ∀ f, FrameWellFormed S f → ∀ st₀, st₀.env.calldata = f.bytes → st₀.env.static = true →
    ∀ V' st' o, Midfall.Yul.Bridge.Run honestCalls gasOracle (S.evaluatorRuntime) st₀ V' st' o →
      (∃ vals, perIdentityValues S (frameValuation S.plan.memory f) = some vals ∧
         st'.halted = some (.ret, outputBytes S.qext.magic (quotientFold S.plan.qplan (yOf S f) vals)))
      ∨ (∃ d, st'.halted = some (.revert, d))
  where outputBytes magic (negNu, buckets) := BE32 magic ‖ BE32 negNu ‖ buckets.map BE32 (Halo2QuotientEvaluator.sol:156-167)
  and perIdentityValues := evalExprρ over globalIdentities (inline/native/tail identities are
  specified by their `expr`, their Yul `lines` path being the named exclusion). -/
```
hypotheses:
- FrameWellFormed - pins program+constants (adversarial frames interpret attacker bytecode) and canonical operands (Yul PUSH_MEM vs fqFromU256 divergence)
- static = true - production uses staticcall (QuotientAndLinearization.yul:35); trace renders use call
- Direct lowering: same post for the direct block (direct_correct, M10, quotientLowering = .direct, not o.quotient)
non-vacuity: with the VK window unpinned, a frame carrying bytecode [PUSH_CONST 0, FOLD_MAIN] makes the evaluator return a value unrelated to the plan while the statement would still have to hold.

### points_subgroup_checked (two layers)  (theorem-sorry; generator layer provable-now; semantic layer needs Midfall.Yul.Bridge call trace; M5 (generator layer), M7 (semantic layer)) — formal/Midfall/Lowering/Calldata.lean (generator layer) + Obligations.lean (semantic layer)
```lean
/-- Generator layer (statable now, near-definitional): coverage validation says every absorbed
    G1 slot reappears among the later G1MSM/pairing inputs and the count matches the layout. -/
theorem points_subgroup_checked_generator (meta_ : Midfall.Generator.ConstraintSystemMeta)
    (data : Midfall.Generator.Data) (memory : Midfall.Generator.VerifierMemoryLayout)
    (L : ProofCalldataLayout)
    (h : Midfall.Generator.validateAbsorbedG1PrecompileCoverage meta_ data memory L = .ok (.ok ())) :
    (Midfall.Generator.proofAbsorbedG1s meta_ data memory).length = L.totalG1Count ∧
    ∀ t ∈ Midfall.Generator.proofAbsorbedG1s meta_ data memory,
      ∃ u, Midfall.Generator.precompileValidatedG1s meta_ data memory = .ok u ∧
        ∃ v ∈ u, Midfall.Generator.ecPointBeq t.point v.point = true := by sorry

/- Semantic layer (Obligations field, needs the Bridge call trace):
  points_subgroup_checked : ∀ cd ms instW, decodeCalldata … cd = some (ms, instW) →
    ∀ run returning, ∀ i, ms[i] = .g1 Q → ∃ call ∈ run.precompileCalls, call.target ∈ {0x0c, 0x0f} ∧
      E.g1.toEip Q is a 128-byte-aligned sub-slice of call.input
  (G1ADD 0x0b does NOT subgroup-check, PLAN.md:567, so it is excluded from the targets). -/
```
hypotheses:
- R-48: the LayoutKats fixture has all PCS bases at 0, so pointer comparisons are vacuous there; the gate must use a fixture with distinct bases
non-vacuity: a validator that forgot f_com or pi (Kzg.lean:993 order) fails the count equality against totalG1Count = commitmentG1Count + 1 + 1.


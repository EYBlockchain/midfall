# DESIGN 0: Per-partial contracts and the L0 snapshot: Checkpoint / Snapshot / Inv design over VerifierMemoryLayout pointers, the minimal R1-faithful Exec refactor that names the phase values, the forall-runs StmtsContract layer the vendored Contract.lean lacks, the side conditions each partial needs, and finalPairing_spec in full (ec_pairing frame with the FinalPairing.yul:88 swap, Eip2537.Holds, the lift of Spec.Lemmas.pairing_reorder to DualMSM.check, accumulator arm via alphaOf). Ground truth: survey.md items (16)-(21), critic.md, and the source files read directly (Verifier.lean:796-969, MultiOpen.lean:201-252, Layout.lean:903-971, vendored Contract.lean/BigStep.lean, Curve.lean, Spec/Lemmas.lean, FinalPairing.yul, AssemblyHelpers.yul:1-310, Lagrange.yul, VkLoading.yul, TranscriptProofParser.yul, QuotientAndLinearization.yul, Pcs.yul, kzg/mod.rs block 6, quotient.rs structured_lookup_loop_block, yul_emit.rs:425-554, Externals.lean:740-964). NEW CONFIRMED FINDING (orchestrator item C asked for it): the contract never inverts f_j(x)+beta - both the inline evaluator (yul_emit.rs:509-554) and the structured lookup block (quotient.rs:1830-1860) compute the helper identity as h*prod - sum_i prefix_i*suffix_i - while Lean Logup.expressions (Logup.lean:279) and Rust logup.rs:460 panic there. So on the bad set {x : some f_j(x)+beta = 0} the contract ACCEPTS an honest proof and Lean/Rust abort: verifier_sound (contract returns -> Lean accepts) is FALSE for all H without a side condition, mirroring the x^n = 1 completeness defect (R-2). Also confirmed: X_N_MINUS_1_INV_MPTR has no consumer in any production template or emitter (grep of kzg/mod.rs, quotient.rs, QuotientNumeratorBlock.yul, quotient_numerator/*.rs is empty), so Inv must treat it as a contract-only don't-care; Lean has no counterpart (lIRange never inverts x^n-1).

## files
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Yul/Contracts.lean
The forall-runs partial-correctness layer the vendored Contract.lean lacks: StmtContractAll / StmtsContractAll / ExprContractAll (every derivation from a pre state satisfies post), the Step inversion lemmas they need (stmts_cons_inv, cond_inv, switch_inv, call_inv, loop_inv), and the composition lemmas: cons_split (halting head), append, block, cond, switch, callUser, countdown_halting, plus of_det (existential StmtsContract + Run.det-style determinism gives the universal form). Dialect-generic over {D : Dialect} [DecidableEq D.Value] exactly like the vendor file, so it instantiates at Bridge.Dialect calls gas.
imports: YulSemantics.BigStep, YulSemantics.Contract, YulSemantics.Determinism
hazards:
- Do not edit vendor/yul-semantics (pinned fork); add the layer under Midfall/Yul.
- Every use at the open dialect must write (D := Midfall.Yul.Bridge.Dialect calls gas) explicitly: Block D.Op does not determine D.
- Non-vacuity gate: StmtsContractAll funs [] (fun _ _ => True) (fun _ _ _ _ _ => False) must be refutable via Step.seqNil, otherwise the layer is trivially satisfiable.
- Comments must not contain apostrophes or the s-word (scripts/lean_grep.py char-literal hazard).
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Lowering/Checkpoint.lean
Checkpoint inductive (.start .vk .transcript .lagrange .quotient .pcs .pairing), Checkpoint.idx / le / next, Partial inductive (the 7 verifier partials), and Checkpoint.liveAt : only MemoryLifetime.permanent regions carry facts across a checkpoint boundary (D-P18: 54 same-byte different-phase pairs; every MemoryPhase scratch is dead between partials).
imports: Midfall.Generator.Layout
hazards:
- MemoryPhase (Layout.lean:407) derives only BEq/Ord and MemoryLifetime only BEq: case-split, do not rely on LawfulBEq.
- Checkpoint must NOT be MemoryPhase: the 16 MemoryPhase constructors are scratch lifetimes, not phase boundaries.
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Lowering/Snapshot.lean
Snapshot record of every L0 intermediate the contract materialises (trace, quotient limb coms, x/splittingFactor/xn, evals, l0/lLast/lBlind/instanceEval, expressions/linCom/queries, x1..x4, fCom, qEvalsOnX3, fEval, v, finalCom, pi, dual, optional acc), snapshotOf computing it from the refactored Exec phase functions (same schedule, no second copy), and snapshotOf_prepareMsgs tying it to prepareMsgs.
imports: Midfall.Halo2.Exec.Native, Midfall.Halo2.Exec.Verifier, Midfall.Halo2.Exec.Kzg.MultiOpen, Midfall.Halo2.Exec.Accumulator
hazards:
- Depends on the Exec refactor (Verifier.readAlgebra / lagrangeTriple / linearize, MultiPrepare.phaseA/B/C) landing first; without it every value is a do-block local.
- prepareMsgs collapses multiPrepare Fault.error to Error.opening (R-8): the agreement lemma is two-part (ok-case value equality; isOk equality), not a plain equation.
- Gt is phantom in DualMSM/KzgAcc: Snapshot takes (p G1 G2 Gt) and every call site writes (Gₜ := Gₜ).
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Lowering/Inv.lean
PlanView (the five LoweringPlan fields that exist today plus k/numInstances/numNegLagranges/hasAccumulator), byte-address helpers over VerifierMemoryLayout Ptr fields (ptrAddr := Value.asUsizeNat (ptrValue _)), holdsFr/holdsG1/holdsG1Region predicates over EVM.loadWord/readBytes, EnvAgrees (p = FR_MODULUS, truncation width 16, delta literal, domain facts, nG2Prepared/sG2Prepared, VK header image), ChallengesGood (bad-set side conditions), and Inv : Checkpoint -> PlanView -> Snapshot -> VEnv -> EvmState -> Prop clause by clause.
imports: Midfall.Lowering.Checkpoint, Midfall.Lowering.Snapshot, Midfall.Generator.Layout, Midfall.Generator.LayoutMemory, Midfall.Generator.Models, Midfall.Generator.Abi, Midfall.Generator.Templates, YulSemantics.Dialect.EVMExec
hazards:
- Ptr arithmetic is word-wise (Encoding.lean:249/276): never add byte offsets to a Ptr; convert first with ptrAddr.
- Lifetime scoping: Inv k may only mention bytes inside permanent regions (vk_payload, challenge_slots, theta block, q_eval_cptr_slot, g1_identity, decoded_evals, decompressed_commitments). TRANSCRIPT_MPTR = RETURN_MPTR = acc batch ptr = 0x1000 overlap by design.
- VEnv must be part of Inv: r, success, buf_len, proof_cptr, lagrange_precompile_failed are Yul locals, not memory.
- Name clashes: Midfall.Generator.Word (pointer) vs Midfall.Word256; Midfall.Generator.g1Bytes vs Midfall.Yul.g1Bytes; qualify.
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Lowering/Partials.lean
The per-partial obligations as a Prop structure (PartialSpecs) over an abstract Surface.blk : Partial -> PlanView -> Block EVM.Op, in forall-runs StmtsContractAll form with the hoisted funs and VEnv-aware pre: vkLoading/transcriptParser/lagrange/quotientLin/pcs/finalPairing/traceReturn _sound (permissive calls, revert-or-Inv-next) and _progress (honest calls, Inv-next, with ChallengesGood where needed). finalPairing_spec in full (noAcc and acc arms). abiTrue.
imports: Midfall.Lowering.Inv, Midfall.Yul.Contracts, Midfall.Yul.Bridge, Midfall.Assumptions.Eip2537, Midfall.Halo2.Spec.PairingLift
hazards:
- No Lean function returns the Yul AST of any verifier partial today (P-13 draft): blk is an abstract field; Pcs body is text (Kzg.lean:1320).
- funs must be hoist D S.main :: outer (AssemblyHelpers functions live at the top of the main assembly block; fail(...) is called from every partial).
- Free Solidity constants (FR_MODULUS, *_MPTR, ERR_*) are unbound in the AST: blk must be the constant-substituted block (bindLocals as substitution, not let-binding).
- traceReturn and finalPairing specs hold only for production renders (trace returns iszero(iszero(success))).
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Assumptions/Eip2537.lean
Eip2537.Holds: the named hypothesis relating Midfall.Yul.PairingProduct, g1MsmOutput and g1AddOutput to AdmissiblePairing through E.g1.toEip and an abstract G2 encoder encG2 (no G2 codec exists in Common; the only encoder is Generator.VkPointCodecs.g2Repr + g2ToU256s), plus codec-shape facts (toEip output passes g1Of?/g1PointMsmValid; accepted frames decode).
imports: Midfall.Common.Curve, Midfall.Common.Codec, Midfall.Halo2.Exec.Native, Midfall.Yul.Externals
hazards:
- Externals.lean has zero theorems; nothing there may be cited as proved.
- pairingFrame is caller-ordered; the swap is at FinalPairing.yul:88, not in AssemblyHelpers (stale Spec/Lemmas.lean:19-20 comment).
- Non-vacuity example must use p-independent witnesses (P2 = g1, Q2 = g2^-1 vs P2 = g1^2), not 2*t = 0 which depends on p != 2.
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Halo2/Spec/PairingLift.lean
Provable-now algebra: every G1 element is a ZMod p multiple of P.g1 (prime order + hG1), DualMSM.check_iff_rustEq (lift of the exponent form), pairingFrame_iff_contractEq under Eip2537.Holds, and finalPairing_check_bridge = pairing_reorder composed with both lifts. Also batchedCheck_iff via dualMsm_scale_check for the S5 side.
imports: Midfall.Halo2.Spec.Lemmas, Midfall.Halo2.Exec.Kzg.Msm, Midfall.Halo2.Exec.Accumulator, Midfall.Assumptions.Eip2537
hazards:
- Must not import Midfall.Instances.* (D-P17 gate greps ^(theorem|lemma)).
- Use P.decEqGₜ explicitly; do not add [DecidableEq] binders (D-P7).
- Mathlib names to confirm with #check: isCyclic_of_prime_card (used by ArkLib PrimeOrder.lean:35, exists), orderOf_eq_prime_iff (OrderOfElement.lean:533, exists), Int.cast_smul_eq_zsmul (Mathlib/Algebra/Module/NatInt.lean, name unverified), smul_eq_zero over a DivisionRing (NoZeroSMulDivisors instance, name unverified).
### /Users/Julien.Coolen/nightfall/midfall/formal/Midfall/Halo2/Exec/Verifier.lean
R1-faithful refactor: move verifyAlgebraicConstraints :283-439 into Verifier.readAlgebra returning an AlgebraRead record, the Lagrange prelude mod.rs:509-515 into Verifier.lagrangeTriple (called by partiallyEvaluateIdentities), and :475-647 into Verifier.linearize; verifyAlgebraicConstraints becomes their composition with the same statement order and the same R-8 collapse. Same for Kzg/MultiOpen.lean: MultiPrepare.phaseA/phaseB/phaseC records with multiPrepare := their composition.
imports: 
hazards:
- Rule R1: no computation may change; evidence is that every existing #eval KAT in Verifier.lean, MultiOpen.lean and Native.lean prints the same token, and the conformance exe (Conformance.**) replays identically.
- The alternative (re-running a transcript prefix in the theorem file to recover x) is a second copy of the Fiat-Shamir schedule, the R-30/R-32 drift hazard; rejected.

## disagreements
- Inv arity: the orchestrator writes Inv : Checkpoint -> PlanView -> Snapshot -> EvmState -> Prop. The partials read Yul LOCALS (r, success, buf_len, proof_cptr, lagrange_precompile_failed) that live in the VEnv, not in memory, and ec_pairing/TraceReturn branch on `success`. Inv must take the VEnv: Inv E params k PV Snap V st (and `D := Bridge.Dialect calls gas` is a parameter because VEnv D is dialect-indexed, though reducibly List (String × U256)).
- Item C: the orchestrator asked whether the contract accepts when f_j(x)+beta = 0. Checked in source: both the inline evaluator (yul_emit.rs:425-554, partial[j] = prefix*suffix) and the structured lookup block (quotient.rs:1830-1860) avoid inversion; the k = 1 path (quotient.rs:1779) never inverts either. So the contract accepts an honest proof on that bad set and Lean/Rust panic. verifier_sound needs the hnopanic (or ChallengesGood.logupNoPanic) hypothesis for every H; it is not only completeness that needs a side condition. This should be recorded next to R-2 as its soundness-direction twin.
- finalPairing_spec cannot be the PLAN's `RunContract (blk …) (Inv .start)`: it is a slice of the main assembly block that reads PAIRING_LHS/RHS, G2_BASE, NEG_S_G2 and `success`. It must be a StmtsContractAll over `hoist S.main :: outer` with Inv .pcs as pre, and Eip2537.Holds must be stated over an abstract encG2 because Common has no G2 codec (only Generator.VkPointCodecs.g2Repr + g2ToU256s, Except-valued). The pulled-forward statement is writable today over an abstract Surface.blk; the proof waits for P-13 (AssemblyHelpers + FinalPairing ASTs) and P-BR.
- Snapshot vs Exec: the orchestrator offered 'a minimal faithful refactor OR an alternative that avoids it'. The only alternative (recompute x and friends by re-running a transcript prefix in the theorem file) is a second copy of the Fiat-Shamir schedule, the R-30/R-32 drift hazard that D-P9 and decodeRust were designed to avoid. Recommend the record-returning refactor (readAlgebra / lagrangeTriple / linearize, MultiPrepare.phaseA/B/C) with the existing KATs and the conformance replay as the R1 evidence; no theorem is needed because the old functions become definitionally the composition.
- Checkpoint liveness: the orchestrator's 'only Permanent regions carry cross-phase facts' is right, but one slot is suspicious: SELECTOR_ACC (selectorAccMptr : Nat) is written by the quotient phase and READ by PCS block 5. If LayoutMemory.new registers it under MemoryPhase.quotientVm, Inv .quotient cannot legally mention it and the quotient→pcs handoff must go through a phase-scoped side predicate (or the layout is wrong). Must be checked against LayoutMemory.lean:140-300 before Inv is frozen.
- X_N_MINUS_1_INV_MPTR: PLAN/Snapshot lists it among L0 values; it has no production consumer (grep of kzg/mod.rs, quotient.rs, QuotientNumeratorBlock.yul, quotient_numerator/*.rs is empty) and no Lean counterpart (lIRange computes (xn-1)*barycentricWeight, never (xn-1)^-1). Inv should leave it unconstrained rather than invent a Lean value.
- Statement shape: the orchestrator groups all unported-dependent statements into one `structure LoweringCorrect`. The per-partial obligations need the forall-runs layer and Bridge imports that the headline statements do not; keep them in Midfall/Lowering/Partials.lean as `PartialSpecs` and let LoweringCorrect carry a field `partials : PartialSpecs S E params …` - otherwise Obligations.lean inherits every Yul import and the D-P17 grep surface grows.

## open decisions
- Bad-set side conditions (R-2 both directions): adopt explicit hypotheses (ChallengesGood.xNotRoot for completeness, hnopanic/logupNoPanic for soundness) rather than widening ContractRef to include a domain check or reading Fault.panic as 'accept'. Recommended: explicit hypotheses, recorded in REVIEW as the R-2 soundness twin.
- Exec refactor sign-off (R1): approve the record-returning split of verifyAlgebraicConstraints and multiPrepare with KATs + conformance replay as the faithfulness gate. Recommended: approve; the alternative duplicates the schedule.
- D-P18 Supported.layout: option 1 (map.WellFormed ∧ validate = .ok ()) stated as a Prop field with `(… ).isOk = true` for decidability. Recommended: option 1.
- X_N_MINUS_1_INV_MPTR: treat as contract-only don't-care in Inv (no production consumer, no Lean value). Recommended: yes, with a comment citing the grep.
- Inv arity includes the VEnv and the dialect parameter; PartialSpecs live in Midfall/Lowering/Partials.lean (not Obligations.lean). Recommended: yes.
- Midfall.Halo2.fixedBases "-G" ↦ (1 : G₁)⁻¹ defect: fix in Exec (take the generator) or keep the table as a parameter everywhere. Recommended: fix in Exec with a KAT, and still take tbl as a parameter in ContractRefAcceptsAcc.
- CI tooling: checks.sh sorts `found` numerically and `listed` lexicographically; a many-hole theorem file must keep its holes in one digit band or checks.sh must sort both the same way. Recommended: fix checks.sh (one-line sort change) and add owner() arms in scripts/gen_sorry.sh for the new files.
- G2 encoder: finalPairing_spec and Eip2537.Holds are stated over an abstract encG2 : G₂ → Bytes; the generator's g2ToU256s ∘ g2Repr is Except-valued. Recommended: accept the abstraction now, add the compatibility hypothesis when VkPointCodecs is bridged.

## proof plan
### Forall-runs contract layer: Midfall/Yul/Contracts.lean with StmtsContractAll and the composition lemmas (Step inversions, cons_split, append, block, cond, switch, callUser, countdown_halting, of_det). [M4-Lean] est 3-4 days
prereqs: vendored BigStep/Contract/Determinism (present)
lemmas:
- Step.stmts_cons_inv
- Step.stmts_append_inv
- Step.cond_inv
- Step.switch_inv (selectSwitch functional)
- Step.call_inv
- Step.loop_inv (7 arms)
- StmtsContractAll.cons_split
- StmtsContractAll.append
- StmtsContractAll.block
- StmtContractAll.cond
- StmtContractAll.switch
- ExprContractAll.callUser
- ExecLoopAll.countdown_halting
- StmtsContractAll.of_det
risks:
- Inversion on the indexed Step family at Code/Res indices may need `generalize` of the index before `cases` (Lean 4.35 dependent elimination); mitigate with explicit index equations.
- Loop halting arms are 7; keep one lemma per arm.
evidence: Refutation example for the trivial contract (seqNil); cons_split applied to [revert-stmt, anything] proves the revert arm where the vendored cons cannot (cons requires head .normal).
### Phase-4a algebra: Midfall/Halo2/Spec/PairingLift.lean (exists_zmod_smul_generator, DualMSM_check_iff_rustEq, pairingFrame_iff_contractEq, finalPairing_check_bridge, batchedCheck_iff via dualMsm_scale_check) + Midfall/Assumptions/Eip2537.lean. [Phase 4a / pulled-forward prerequisite] est 2-3 days
prereqs: Spec/Lemmas.lean (present); Externals.lean names g1Of?/g2Of?/g1PointMsmValid/g2PointValid/pairingFrame/g1MsmFrame (present)
lemmas:
- zmod_smul_eq_zsmul
- exists_zmod_smul_generator (G₁ and G₂)
- decideBool_eq_true_iff
- MSMKZG.eval_fromBase (eval of a one-term MSM)
- DualMSM_check_iff_rustEq
- pairingFrame_iff_contractEq
- finalPairing_check_bridge
- batchedCheck_iff_rustEq (needs MSMKZG addMsm additivity under Wf, owed by the Msm area)
risks:
- Mathlib names unverified in this tree: Int.cast_smul_eq_zsmul, the NoZeroSMulDivisors instance for a DivisionRing scalar (smul_eq_zero); run #check before relying.
- AdmissiblePairing.e is a curried LinearMap: map_smul must be applied in both arguments (LinearMap.map_smul then LinearMap.smul_apply).
evidence: ZMod 17 examples: the unswapped frame order is refuted at xL = 1, xR = 1, s = 2; #print axioms of finalPairing_check_bridge must list only propext/Classical.choice/Quot.sound.
### Exec refactor (R1): Verifier.AlgebraRead/readAlgebra/lagrangeTriple/linearize and MultiPrepare.phaseA/B/C; verifyAlgebraicConstraints and multiPrepare become compositions. [M5 prerequisite] est 1-2 days
prereqs: Exec core builds (Verifier/Native/Msm have oleans)
lemmas:
- none - definitional; partiallyEvaluateIdentities calls lagrangeTriple so its body is unchanged modulo the extracted let
risks:
- R1 review: any reordering is a different challenge stream; the KAT tokens and the Conformance exe are the gate.
- lagrangeTriple returns (lLast, lBlind, l0) - keep the Rust slot order (mod.rs:509-515) in the doc comment so Inv .lagrange cites the right slots (Lagrange.yul:77-79).
evidence: All #eval KATs in Verifier.lean/MultiOpen.lean/Native.lean unchanged; `lake build` green; conformance replay identical.
### Checkpoint.lean, Snapshot.lean (snapshotOf, snapshotOf_prepareMsgs), Inv.lean (PlanView, EnvAgrees, ChallengesGood, Inv) with satisfiability/perturbation gates. [M5] est 4-5 days
prereqs: step 3; LayoutMemory.lean region list for the SELECTOR_ACC lifetime question
lemmas:
- snapshotOf_prepareMsgs (unfold StateT.run of the composition; R-8 collapse case split)
- ptrAddr_new_theta (for layouts from VerifierMemoryLayout.new, ptrAddr xMptr = ptrAddr thetaMptr + 32·ThetaSlot.x.word; survey: all Ptr fields are ptrMemory (valueFromNat _))
- Inv_mono (k₁ ≤ k₂ → Inv k₂ → Inv k₁)
- vkDigest_word_eq_frWord (feToU256 (bytesToNats (frToRepr r)) = .ok (frWord r); Vk.lean:763, owed by the critic)
risks:
- reversedEvalsOf (the Data.new eval order) and selectorBucketsOf (the groupedAdd selector scalars) need the Encoding area's bridge; stub them as Surface fields if late.
- If SELECTOR_ACC is phase-scoped, split Inv .quotient into a permanent part and a quotient→pcs carry predicate.
evidence: Inv is satisfiable on a hand-built EvmState for a 1-instance fixture and refuted when the pairingLhs/pairingRhs words are swapped or when halted is set; ChallengesGood exhibits both a satisfying and a violating x over ZMod 17.
### Pulled-forward finalPairing_spec: Partials.lean PartialSpecs skeleton, finalPairing_sound_noAcc/progress/acc and traceReturn_spec statements; proofs over the AssemblyHelpers.yul + FinalPairing.yul ASTs once P-13 delivers them. [right after M3 (PLAN 14.4)] est 1.5-2 weeks after P-13/P-BR land
prereqs: P-BR Bridge.lean (Dialect, honestCalls, honestResponds, withKeccak, keccakOf invariance); P-13: AssemblyHelpers.yul (ec_pairing, fail) and FinalPairing.yul as Block EVM.Op with constants substituted; steps 1, 2, 4
lemmas:
- ec_pairing_contract (StmtsContractAll of the function body: mcopy frame, staticcall 0x0f, returndatasize check, eq(mload, 1), fail/ret := 1)
- mcopy_frame_bytes (readBytes after four mcopy = pairingFrame of the two slot images and the two VK G2 images)
- staticcall_pairing_inv (externalCall at 0x0f under Permissive → success → returndata = pairingOutputWord (product frame))
- fail_reverts (fail(sel) halts with .revert and 4-byte data)
- finalPairing_check_bridge (step 2)
- acc arm: alpha_preimage_bytes (mstore/mcopy sequence = alphaOf preimage), keccak_mod_r_eq_alphaOf, g1msm_then_g1add_slot (slot := Q + gsmul α A)
risks:
- The vendored dialect has no memoryguard/mcopy issue? mcopy IS in EVM.Op (EVMOp.lean:27 lists mcopy) - fine; but staticcall inside a user function body (ec_pairing) needs ExprContractAll.callUser plus the staticcall builtin relation (EVMExec.lean:906-910).
- Gas: PAIRING_GAS_2PAIR literal is irrelevant under ExternalGas.ofFun but appears as an argument; Permissive ignores req.gas.
evidence: finalPairing_sound_noAcc is refuted (becomes unprovable) if the frame order in the block is unswapped - the bridge lemma's ZMod 17 example; trace-render block falsifies the success = 1 conjunct.
### M5 early partials: vkLoading (embedded VK), transcriptParser, lagrange - statements in PartialSpecs, proofs once their ASTs exist. [M5] est 3-4 weeks
prereqs: P-13 ASTs for VkLoading.yul, TranscriptProofParser.yul, Lagrange.yul; calldata area: decodeCalldata over raw Word256 and the repack/toEip relation; Bridge: withKeccak adapter lemma (keccakOf (readBytes …) = H (bytes)), modexp relation for batch_invert
lemmas:
- vkLoading: mstore_sequence_image (the embedded mstores write PV.vk.bytes at vkMptr), header_words_match (num_instances/k/has_acc/… equalities by construction from the same plan), calldata_shape_exact (VkLoading.yul:101-109)
- transcriptParser: squeeze_to_eq_squeezeChallenge (keccak of the buffer = Transcript.squeeze state; mod r = frOfDigest), common_word/common_uncompressed_g1 = Transcript.common (frToInputBE / toEip), x3_mask_eq_truncate (under truncWidth = 16), parser_consumes_exactly (proof_cptr = NUM_INSTANCE_CPTR ↔ assertEmpty), instance_canonical (lt(inst_be, r) ↔ frOfRepr?-style canonicality, modulus)
- lagrange: xn_by_squaring (k squarings = powVartime x n under domainN), denoms_window (pow_of_omega walk = rotateOmega with omegaInv^l·ω^j under omegaInvMul/negLagranges), batch_invert_contract (modexp inverse; zero → ret = 0; non-canonical → ret = 0), lIRange_eq_contract (under xNotRoot ∧ omegaOrder ∧ baryWeight), instance_eval_eq (noRotInst: Σ l_i·inst_i = computeInnerProduct)
risks:
- TranscriptProofParser has ~12 loops; the countdown lemmas must be instantiated per region with the ProofReadPlan order (Protocol.lean:315) - the schedule equality with parseTrace is the heart of M5.
- lagrange: Lean's two lIRange calls (window for instances; -(bf+1)..0 for l_last/l_blind/l_0) vs the contract's single fused denominators array need an index bijection lemma.
evidence: Perturbation gates: a transcript block that absorbs the committed_pi as 48 bytes (old emitter) breaks squeeze equality on the first challenge; a lagrange block without the gp = 0 check falsifies lagrange_sound's extra conjunct.
### quotientLin and pcs partials (M6/M7) - statements only in this scope; proofs owned by the QVM and PCS areas. [M6/M7] est see QVM/PCS areas
prereqs: P-09 QVM yul emitter / per-identity bridge; AST-producing PCS emitter (R-42 option A) or yul% of its text; ChallengesGood.logupNoPanic formulation agreed
lemmas:
- quotientLin: linearization_prep (x_split = x^(n-1), 1 - x^n), quotientEval_eq_linCom_eval (Horner y-order vs reverse fold, R-16/R-19), buckets_eq_groupedAdd
- pcs: block2/5 truncated powers = truncatedPowers (truncWidth), block4 fEval (scalar_inv revert ↔ fEval panic, both reject), block5 finalCom/v, block6 slot equations (−v·G via G1MSM, G1ADD twice: Eip2537.Holds.g1Msm1/g1Add)
risks:
- pcs block 6 uses the pcs_pairing_scratch at 0x1000 (phase pcsPairing) - Inv .pcs must not mention it.
evidence: Inv .quotient's quotientEval clause is refuted if the sign convention (−ν_y(x)) is dropped.
### Composition: verifier_sound / verifier_complete from PartialSpecs via StmtsContractAll.append over the seven slices, then the headline statements with hnopanic/hgood. [M7] est 1 week
prereqs: all partial proofs; Bridge.RunCommitted.det for the completeness ∀-runs reading; decodeCalldata/LeanAccepts from the calldata area
lemmas:
- main_block_is_concat (S.main = helpers ++ [let r, let success] ++ blk vkLoading ++ … ++ blk traceReturn)
- Inv_start_of_initState
- append of the seven PartialSound facts
- snapshot_exists_of_nopanic (hnopanic → ∃ Snap, snapshotOf = .ok Snap)
risks:
- The PLAN's RunVerifier prepends headGuard and bindLocals; the memory-guard revert (Halo2Verifier.sol:188-191) is an extra revert arm before Inv .start.
evidence: verifier_sound without hnopanic must be shown unprovable by the logup counterexample recorded as a comment and a KAT on Logup.expressions with a zero denominator.

## declarations
### YulSemantics.StmtsContractAll / StmtContractAll / ExprContractAll  (def; statable-now; M4-Lean (prerequisite of every *_spec)) — formal/Midfall/Yul/Contracts.lean
```lean
namespace YulSemantics
variable {D : Dialect} [DecidableEq D.Value]

/-- Partial correctness over EVERY derivation: whenever `pre` holds, every run of
    `stmts` ends in a state and outcome satisfying `post`. The vendored
    `StmtsContract` (Contract.lean:94) is existential (some run) and says nothing
    about all runs under a relational `calls`, which is what verifier_sound needs. -/
def StmtsContractAll (funs : FunEnv D) (stmts : Block D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmts D funs V st stmts V' st' o → post V st V' st' o

def StmtContractAll (funs : FunEnv D) (s : Stmt D.Op)
    (pre : VEnv D → D.State → Prop)
    (post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop) : Prop :=
  ∀ V st, pre V st → ∀ V' st' o, ExecStmt D funs V st s V' st' o → post V st V' st' o

/-- Expression form: every evaluation result (values or halt) satisfies `post`. -/
def ExprContractAll (funs : FunEnv D) (e : Expr D.Op)
    (pre : VEnv D → D.State → Prop) (post : VEnv D → D.State → EResult D → Prop) : Prop :=
  ∀ V st, pre V st → ∀ r, EvalExpr D funs V st e r → post V st r
end YulSemantics
```
hypotheses:
- [DecidableEq D.Value] - required by Step/ExecStmts (BigStep.lean:164); resolves at evmWithExternal because Value := U256 reducibly (survey Yul area).
non-vacuity: example : ¬ StmtsContractAll (D := EVM.evm) [] [] (fun _ _ => True) (fun _ _ _ _ _ => False) := fun h => h [] EvmState.init trivial [] _ .normal Step.seqNil; a definition that quantified over no derivation would make this example fail.

### StmtsContractAll composition lemmas (cons_split, append, block, cond, switch, callUser, countdown_halting, of_det) + Step inversion lemmas  (lemma-provable-now; provable-now; M4-Lean) — formal/Midfall/Yul/Contracts.lean
```lean
namespace YulSemantics
variable {D : Dialect} [DecidableEq D.Value]

/-- Inversion of a sequence derivation (the only two rules are seqCons/seqStop). -/
theorem Step.stmts_cons_inv {funs V st s ss V' st' o}
    (h : ExecStmts D funs V st (s :: ss) V' st' o) :
    (∃ V₁ st₁, ExecStmt D funs V st s V₁ st₁ .normal ∧ ExecStmts D funs V₁ st₁ ss V' st' o) ∨
    (ExecStmt D funs V st s V' st' o ∧ o ≠ .normal) := by
  cases h with
  | seqCons h₁ h₂ => exact Or.inl ⟨_, _, h₁, h₂⟩
  | seqStop h₁ hne => exact Or.inr ⟨h₁, hne⟩

/-- Halting-head cons: the head either continues normally into `mid` or stops
    with the final postcondition already established (the revert arm). -/
theorem StmtsContractAll.cons_split {funs : FunEnv D} {s : Stmt D.Op} {ss : Block D.Op}
    {pre mid : VEnv D → D.State → Prop}
    {post : VEnv D → D.State → VEnv D → D.State → Outcome → Prop}
    (head : StmtContractAll funs s pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (tail : ∀ V st, pre V st →
      StmtsContractAll funs ss mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll funs (s :: ss) pre post := by
  intro V st hpre V' st' o hrun
  rcases Step.stmts_cons_inv hrun with ⟨V₁, st₁, h₁, h₂⟩ | ⟨h₁, hne⟩
  · rcases head V st hpre V₁ st₁ .normal h₁ with ⟨_, hmid⟩ | ⟨hne, _⟩
    · exact tail V st hpre V₁ st₁ hmid V' st' o h₂
    · exact absurd rfl hne
  · rcases head V st hpre V' st' o h₁ with ⟨heq, _⟩ | ⟨_, hpost⟩
    · exact absurd heq hne
    · exact hpost

/-- Needed because each partial is a SLICE of the main block, not a block. -/
theorem StmtsContractAll.append {funs} {ss₁ ss₂ : Block D.Op} {pre mid post}
    (h₁ : StmtsContractAll funs ss₁ pre (fun V st V' st' o =>
      (o = .normal ∧ mid V' st') ∨ (o ≠ .normal ∧ post V st V' st' o)))
    (h₂ : ∀ V st, pre V st → StmtsContractAll funs ss₂ mid (fun _ _ => post V st)) :
    StmtsContractAll funs (ss₁ ++ ss₂) pre post := by
  sorry -- induction on ss₁ via Step.stmts_cons_inv and a stmts_append_inv lemma

-- Also owed (statable now, routine inversions):
--   StmtsContractAll.block   (mirror of StmtsContract.block, restore V V')
--   StmtContractAll.cond     (ExprContractAll on the guard; body contract when cv ≠ zero)
--   StmtContractAll.switch   (selectSwitch is a function: one body per cv)
--   ExprContractAll.callUser (lookupFun funs f = some (decl, cenv) → body contract over
--                             (decl.params.zip argvals) ++ bindZeros D decl.rets)
--   ExecLoopAll.countdown_halting (loopBodyHalt / loopPostHalt / loopCondHalt arms)
--   StmtsContractAll.of_det  (StmtsContract + ∀ op, D.Deterministic op → StmtsContractAll)
end YulSemantics
```
hypotheses:
- None beyond the dialect binders; of_det needs ∀ op, D.Deterministic op (Dialect.lean:135), discharged for Bridge.Dialect by the Bridge lemma under ExternalCalls.Functional and ExternalGas.ofFun (Y-5).
non-vacuity: cons_split must reject a head contract whose mid is False while post is False (so no sequence derivation exists only if the head has none): example on [exprStmt (builtin .revert [..]), x] where the tail is never reached; a wrong lemma that required the head to be .normal (the vendored cons) could not prove the revert arm.

### Midfall.Lowering.Checkpoint / Partial / Checkpoint.liveAt  (inductive; statable-now; M5) — formal/Midfall/Lowering/Checkpoint.lean
```lean
namespace Midfall.Lowering
open Midfall.Generator

/-- The seven boundaries between verifier partials (PLAN 9.5 Inv indices). NOT
    `Generator.MemoryPhase` (Layout.lean:407), which is a 16-way scratch lifetime. -/
inductive Checkpoint
  | start | vk | transcript | lagrange | quotient | pcs | pairing
  deriving DecidableEq, Repr

def Checkpoint.idx : Checkpoint → Nat
  | .start => 0 | .vk => 1 | .transcript => 2 | .lagrange => 3
  | .quotient => 4 | .pcs => 5 | .pairing => 6

instance : LE Checkpoint := ⟨fun a b => a.idx ≤ b.idx⟩

/-- The seven production partials in include order (Halo2Verifier.sol:217-229). -/
inductive Partial
  | vkLoading | transcriptParser | lagrange | quotientLin | pcs | finalPairing | traceReturn
  deriving DecidableEq, Repr

def Partial.pre : Partial → Checkpoint
  | .vkLoading => .start | .transcriptParser => .vk | .lagrange => .transcript
  | .quotientLin => .lagrange | .pcs => .quotient | .finalPairing => .pcs | .traceReturn => .pairing

/-- Which region lifetimes carry facts ACROSS a checkpoint. Every `MemoryPhase`
    scratch is dead between partials (LayoutMemory.lean:909: 54 same-byte,
    different-phase pairs; transcript buffer, pcs scratch, acc batch and return
    buffer all start at 0x1000). Only permanent regions survive. -/
def Checkpoint.liveAt (_ : Checkpoint) : MemoryLifetime → Bool
  | .permanent => true
  | .phase _ => false
end Midfall.Lowering
```
hypotheses:
- None.
non-vacuity: liveAt .pcs (.phase .pcsFixed) = false by rfl: an Inv that claimed ROT_POINTS/X1_POWERS at .pairing would be stated over dead bytes (acc batch at 0x1000 overwrites them) and finalPairing_spec would become unprovable; the gate example pins this.

### Midfall.Halo2.Verifier.AlgebraRead / readAlgebra / lagrangeTriple / linearize and MultiPrepare.PhaseA/B/C (Exec refactor)  (def; statable-now; M5 prerequisite (Exec package, before Snapshot.lean)) — formal/Midfall/Halo2/Exec/Verifier.lean and formal/Midfall/Halo2/Exec/Kzg/MultiOpen.lean
```lean
-- Verifier.lean (inside namespace Verifier, same binders as verifyAlgebraicConstraints)
/-- verifier.rs:283-439 as one named read phase. Bodies are MOVED verbatim; the
    composition below is definitionally the old function (rule R1). -/
structure AlgebraRead (Fr G₁ : Type) where
  quotientLimbComs : Array G₁
  x splittingFactor xn : Fr
  lIS : Array Fr
  instanceEvals adviceEvals : Array (Array Fr)
  fixedEvals : Array Fr
  permutationsCommon : Permutation.CommonEvaluated Fr
  permutationsEvaluated : Array (Permutation.Evaluated Fr G₁)
  lookupsEvaluated : Array (Array (Logup.Evaluated Fr G₁))
  trashcansEvaluated : Array (Array (Trash.Evaluated Fr G₁))

def readAlgebra (g1 : G1Codec G₁) (feat : Features) (vk : VerifyingKey (Fr p) G₁)
    (trace : VerifierTrace (Fr p) G₁) (committed : Array (Array G₁))
    (instances : Array (Array (Array (Fr p)))) : TranscriptM (AlgebraRead (Fr p) G₁)

/-- plonk/mod.rs:509-515, lifted out of partiallyEvaluateIdentities (which now calls it):
    (lLast, lBlind, l0). -/
def lagrangeTriple (vk : VerifyingKey (Fr p) G₁) (x xn : Fr p) :
    Except Fault (Fr p × Fr p × Fr p)

/-- verifier.rs:475-647: expressions, linearization query, multi-open queries. -/
def linearize (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (nbCommitted : Nat) (committed : Array (Array G₁)) (r : AlgebraRead (Fr p) G₁) :
    Except Fault (Array (Option Nat × Fr p) × VerifierQuery (Fr p) G₁ ×
      Array (VerifierQuery (Fr p) G₁))

-- verifyAlgebraicConstraints := shape checks (:260-268) ; let r ← readAlgebra … ;
--   let (_, _, queries) ← StateT.lift (linearize …) ; the R-8 collapse of pcs.multiPrepare.

-- MultiOpen.lean
structure PhaseA where x1 x2 : Fr p; qComs : Array (MSMKZG (Fr p) G₁); qEvalSets pointSets : Array (Array (Fr p))
structure PhaseB where fCom : G₁; x3 : Fr p; qEvalsOnX3 : List (Fr p); fEval : Fr p
structure PhaseC where x4 : Fr p; finalCom : MSMKZG (Fr p) G₁; v : Fr p; pi : G₁; dual : DualMSM (Fr p) G₁ G₂ Gₜ
def MultiPrepare.phaseA (g1 fc feat fewer queries) : TranscriptM PhaseA   -- :210-223
def MultiPrepare.phaseB (g1 fc feat) (a : PhaseA) : TranscriptM PhaseB      -- :225-232
def MultiPrepare.phaseC (g1 fc feat) (a : PhaseA) (b : PhaseB) : TranscriptM PhaseC -- :234-252
-- multiPrepare … := do let a ← phaseA …; let b ← phaseB … a; pure (← phaseC … a b).dual
```
hypotheses:
- None (definitions). Faithfulness evidence: all existing #eval KATs unchanged and the Conformance exe replays identically; this is the R1 gate, not a theorem.
non-vacuity: A refactor that reordered the x3 truncation after the qEvalsOnX3 reads, or dropped the scaledPi addMsm (MultiOpen.lean:247-252 comment), changes KAT tokens in MultiOpen.lean and the conformance replay; the R1 gate is exactly what catches it.

### Midfall.Lowering.Snapshot / snapshotOf / snapshotOf_prepareMsgs  (structure; needs Exec refactor (statable immediately after); M5) — formal/Midfall/Lowering/Snapshot.lean
```lean
namespace Midfall.Lowering
open Midfall.Halo2
variable {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- Every L0 intermediate the contract materialises in memory, in the order the
    verifier produces it. G₂ Gₜ are phantom through DualMSM/KzgAcc (D-P7). -/
structure Snapshot (p : Nat) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type) where
  trace : VerifierTrace (Fr p) G₁              -- theta beta gamma trash y, advice/lookupM/permZ/helper/lookupZ/trash coms
  alg : Verifier.AlgebraRead (Fr p) G₁         -- quotient limb coms, x, splittingFactor, xn, evals
  l0 lLast lBlind : Fr p                       -- L_0, L_LAST, L_BLIND slots
  instanceEval : Fr p                          -- INSTANCE_EVAL = Σ inst_i · l_i(x) (noRotInst)
  expressions : Array (Option Nat × Fr p)      -- partiallyEvaluateIdentities output
  linCom : VerifierQuery (Fr p) G₁             -- QUOTIENT_EVAL := linCom.eval; buckets := its selector scalars
  queries : Array (VerifierQuery (Fr p) G₁)
  a : MultiPrepare.PhaseA (p := p) (G₁ := G₁)  -- x1 x2 qComs qEvalSets pointSets
  b : MultiPrepare.PhaseB (p := p) (G₁ := G₁)  -- fCom x3 (already truncated) qEvalsOnX3 fEval
  c : MultiPrepare.PhaseC (p := p) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) -- x4 finalCom v pi dual
  acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)        -- decodeAcc result in accumulator renders

/-- The snapshot of one message-level run: the SAME schedule prepareMsgs runs
    (Native.lean:255-268), cut at the refactored phase boundaries. -/
def snapshotOf (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁)
    (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) (acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)) :
    Except Fault (Snapshot p G₁ G₂ Gₜ) := do
  let bytes := ms.foldl (init := Bytes.empty) (fun a m => ByteArray.append a (msgWire E m))
  let t0 := Transcript.initWithHash H bytes
  let (trace, t1) ← (parseTrace E.g1 Features.solidity vk #[#[1]] #[#[inst]]).run t0
  let (alg, t2) ← (Verifier.readAlgebra E.g1 Features.solidity vk trace #[#[1]] #[#[inst]]).run t1
  let (lLast, lBlind, l0) ← Verifier.lagrangeTriple vk alg.x alg.xn
  let (expressions, linCom, queries) ← Verifier.linearize E.delta vk trace 1 #[#[1]] alg
  let (a, t3) ← (MultiPrepare.phaseA (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field Features.solidity E.fewerPointSetsRuntime queries).run t2
  let (b, t4) ← (MultiPrepare.phaseB (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field Features.solidity a).run t3
  let (c, t5) ← (MultiPrepare.phaseC E.g1 E.field Features.solidity a b).run t4
  t5.assertEmpty
  let instanceEval := (alg.instanceEvals.getD 0 #[]).getD 0 0   -- single public column, one query at rotation 0 (noRotInst)
  pure { trace, alg, l0, lLast, lBlind, instanceEval, expressions, linCom, queries, a, b, c, acc }

/-- Agreement with prepareMsgs. Two parts because verifyAlgebraicConstraints maps
    every multiPrepare `Fault.error` to `Error.opening` (R-8). -/
theorem snapshotOf_prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk) (inst) (ms) (acc) :
    (∀ S, snapshotOf E H vk inst ms acc = .ok S →
        prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok S.c.dual) ∧
    ((snapshotOf E H vk inst ms acc).isOk = (prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms).isOk) := by
  sorry
end Midfall.Lowering
```
hypotheses:
- None; the theorem is about definitions and follows by unfolding the refactored composition (StateT.run of do-blocks).
non-vacuity: If snapshotOf used Features default instead of Features.solidity (truncatedChallenges false) part 1 fails on any proof whose x3 has a nonzero high 128 bits; if lagrangeTriple were misordered (l0, lLast) the Inv .lagrange clauses would pin the wrong slots and lagrange_spec would be unprovable against Lagrange.yul:77-79.

### Midfall.Lowering.PlanView / EnvAgrees  (structure; statable-now (blsDeltaLiteral and vkG1Words/vkG2Words are small new defs over Halo2VerifyingKey.constants); M5) — formal/Midfall/Lowering/Inv.lean
```lean
namespace Midfall.Lowering
open Midfall.Generator Midfall.Halo2

/-- The LoweringPlan fields that exist today (plan.rs:29 is unported, P-11): what
    Inv and the partial specs read. hasAccumulator mirrors expected_has_accumulator. -/
structure PlanView where
  vk : Halo2VerifyingKey
  vkMptr : Ptr
  memory : VerifierMemoryLayout
  proofLayout : ProofCalldataLayout
  numInstances k numNegLagranges : Nat
  hasAccumulator : Bool
  consts : TemplateConstants

variable {p : Nat} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- What must tie the abstract Lean environment to the literals the contract
    hard-codes. Every arithmetic partial needs `modulus`; each other field is cited
    at the partial that needs it. -/
structure EnvAgrees (E : VerifierEnv p G₁ G₂ Gₜ) (vk : VerifyingKey (Fr p) G₁)
    (PV : PlanView) (params : ParamsVerifierKZG G₁ G₂) (sG2gen : G₂) (encG2 : G₂ → Bytes) : Prop where
  /-- addmod/mulmod/lt(.., r) use the FR_MODULUS literal (Templates.lean:187). -/
  modulus : p = frModulusConstant
  /-- truncate keeps divCeil (divCeil numBits 8) 2 low bytes; the Yul masks 128 bits (critic). -/
  truncWidth : divCeil (divCeil E.field.numBits 8) 2 = 16
  /-- {{ fr_delta }} literal, quotient.rs:1492; the Lean constant does not exist yet. -/
  delta : E.delta = (Nat.cast blsDeltaLiteral : Fr p)
  /-- Lagrange.yul:13 squares k times; Lean uses xn = x^(n-1)·x. -/
  domainN : vk.domain.n = 2 ^ vk.domain.k ∧ vk.domain.k = PV.k
  /-- N_INV := invert(2^k) (Vk.lean:770); Lean uses the imported barycentricWeight. -/
  baryWeight : vk.domain.barycentricWeight = ((2 ^ vk.domain.k : ℕ) : Fr p)⁻¹
  /-- Lagrange.yul:30-35 walks OMEGA_INV_TO_L·ω^j; Lean rotates negative rotations by omegaInv. -/
  omegaInvMul : vk.domain.omegaInv * vk.domain.omega = 1
  omegaOrder : vk.domain.omega ^ vk.domain.n = 1
  negLagranges : PV.numNegLagranges = Int.natAbs (vk.cs.blindingFactors.toOption.getD 0 + 1)
  /-- R-4: ofParams gives g2⁻¹, read gives g2Gen⁻¹; the contract pairs with G2_BASE = P.g₂. -/
  nG2 : params.nG2Prepared = P.g₂⁻¹
  /-- NEG_S_G2_BASE = (ParamsKZG.sG2)⁻¹ (Vk.lean:802-815); check reads sG2Prepared. -/
  sG2 : params.sG2Prepared = sG2gen
  /-- VK header image (vkHeaderTemplateSlotsDefault): words 0..26. -/
  vkDigestWord : PV.vk.constants.getD 0 ("", 0) |>.2 = frWord vk.transcriptRepr
  g1BaseWords  : vkG1Words PV 11 = E.g1.toEip P.g₁
  g2BaseWords  : vkG2Words PV 15 = encG2 P.g₂
  negSG2Words  : vkG2Words PV 23 = encG2 sG2gen⁻¹
end Midfall.Lowering
```
hypotheses:
- modulus - FR_MODULUS literal in every addmod/mulmod and in lt(inst_be, r) (TranscriptProofParser.yul:63); without it Fr p arithmetic and the canonicality checks do not match.
- truncWidth - critic unmentioned constraint 2 (x3 mask at TranscriptProofParser.yul:365, x1/x4 masks Kzg.lean:1367-1379/1626-1633).
- delta - critic unmentioned constraint 3 (QuotientNumeratorBlock.yul:1407).
- domainN/baryWeight/omegaInvMul/omegaOrder - critic unmentioned constraint 4; omegaOrder is needed so that x^n ≠ 1 implies x ≠ ω^i for the batch_invert denominators.
- nG2/sG2 - R-4 and R-11 (survey L0 area), FinalPairing.yul:88 orientation.
- vkDigestWord - R-1: transcriptRepr is imported; the contract hashes the VK_DIGEST word (TranscriptProofParser.yul:26).
non-vacuity: With baryWeight dropped, a vk whose barycentricWeight is 2·n⁻¹ makes Lean L_i values twice the contract ones, and lagrange_spec is false; with omegaOrder dropped, ω of order 2n and x = ω makes the contract revert while x^n = -1 ≠ 1 passes ChallengesGood.

### Midfall.Lowering.ChallengesGood (bad-set side conditions)  (structure; statable-now (logupNoPanic after the refactor); M5 (lagrange), M7 (verifier_sound)) — formal/Midfall/Lowering/Inv.lean
```lean
/-- The finite bad set the squeezed challenges must miss for Lean and the contract
    to agree. R-2 has three manifestations; only the first two DIVERGE between the
    sides, the third (x3 in a point set) is a revert on both sides. -/
structure ChallengesGood (vk : VerifyingKey (Fr p) G₁) (S : Snapshot p G₁ G₂ Gₜ) : Prop where
  /-- Lagrange.yul:93-99 reverts ProofRejected when x^n - 1 = 0 or some x - ω^i = 0;
      Lean lIRange (Domain.lean:251-258) silently yields zeros and ACCEPTS. Completeness. -/
  xNotRoot : S.alg.x ^ vk.domain.n ≠ 1
  /-- The contract computes the lookup helper identity with prefix/suffix products
      (yul_emit.rs:509-554, quotient.rs:1830-1860) and never inverts; Lean
      Logup.expressions panics at logup.rs:460 when f_j(x)+β = 0 (Logup.lean:279).
      There the contract ACCEPTS an honest proof and Lean rejects. Soundness. Stated
      as panic-freedom of the linearization step: the only panic site reachable
      from a parsed proof under Supported is that inversion. -/
  logupNoPanic : ∀ site, Verifier.linearize E.delta vk S.trace 1 #[#[1]] S.alg ≠ .error (Fault.panic site)

/-- Reference: the reachable third manifestation needs no clause. If x3 hits a
    point set, MultiPrepare.fEval panics (kzg/mod.rs:479) and the contract reverts
    NonCanonicalScalar in scalar_inv (AssemblyHelpers.yul:22-23 via kzg/mod.rs:1503);
    both sides reject, so equivalence holds without a hypothesis. -/
```
hypotheses:
- xNotRoot - critic CORRECTION (first R-2 manifestation); needed by lagrange_progress and by every completeness conjunct.
- logupNoPanic - NEW finding above; needed by verifier_sound and by quotientLin_sound (contract normal → Lean value exists).
non-vacuity: example over ZMod 17 with n = 16, ω = 3: x = 3 violates xNotRoot while x = 2 satisfies it (2^16 = 1 in ZMod 17, so also violates; use x = 0: 0^16 = 0 ≠ 1 holds) - the gate shows the predicate is neither always true nor always false.

### Midfall.Lowering.Inv (memory + VEnv invariant per checkpoint)  (def; statable-now modulo tblOf/reversedEvalsOf/selectorBucketsOf (small defs over PlanView and VerifierQuery; reversedEvalsOf needs the Data.new eval order bridge, owed by the Encoding area); M5) — formal/Midfall/Lowering/Inv.lean
```lean
open YulSemantics.EVM in
def ptrAddr (q : Ptr) : Nat := Value.asUsizeNat (ptrValue q)   -- Layout.lean:1010; word-wise Ptr arithmetic never used here
def wordAt (st : EvmState) (a : Nat) : Word256 := loadWord st.memory a       -- EVMExec.lean:320
def bytesAt (st : EvmState) (a n : Nat) : Bytes := ByteArray.mk (readBytes st.memory a n).toArray  -- :337
def holdsFr (st : EvmState) (a : Nat) (x : Fr p) : Prop := wordAt st a = frWord x    -- canonical: frWord x < r
def holdsG1 (E : VerifierEnv p G₁ G₂ Gₜ) (st : EvmState) (a : Nat) (Q : G₁) : Prop :=
  bytesAt st a 128 = E.g1.toEip Q
def holdsG1s (E) (st) (base : Nat) (Qs : Array G₁) : Prop :=
  ∀ i, i < Qs.size → holdsG1 E st (base + 128 * i) (Qs.getD i 1)
def holdsFrs (st) (base : Nat) (xs : Array (Fr p)) : Prop :=
  ∀ i, i < xs.size → holdsFr st (base + 32 * i) (xs.getD i 0)

/-- The Yul locals every partial reads. `D := Bridge.Dialect calls gas`, VEnv D = List (String × U256). -/
def LocalsOk (V : VEnv (Bridge.Dialect calls gas)) : Prop :=
  VEnv.get V "r" = some (BitVec.ofNat 256 p) ∧ (VEnv.get V "success" = some 1 ∨ VEnv.get V "success" = some 0)

/-- Inv k: what memory, locals and state look like at checkpoint k, relative to the
    snapshot S. Clauses accumulate (idx-monotone) and mention ONLY permanent regions
    (Checkpoint.liveAt); every address is a byte address derived from a layout Ptr. -/
def Inv (E : VerifierEnv p G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂) (k : Checkpoint)
    (PV : PlanView) (S : Snapshot p G₁ G₂ Gₜ) (V : VEnv (Bridge.Dialect calls gas))
    (st : EvmState) : Prop :=
  let M := PV.memory
  st.halted = none ∧ LocalsOk (p := p) V ∧
  -- .vk : VK payload image at VK_MPTR (VkLoading.yul:33-56 / :74), exact calldata shape
  (Checkpoint.vk ≤ k →
     bytesAt st (ptrAddr M.vkMptr) PV.vk.len = PV.vk.bytes ∧
     st.env.calldata.length = PV.proofLayout.proofEnd + 32 + 32 * PV.numInstances ∧
     (PV.hasAccumulator = true → ∃ a, S.acc = some a ∧
        holdsG1 E st (ptrAddr M.accLhsMptr) (a.fullyCollapse (tblOf PV)).1 ∧
        holdsG1 E st (ptrAddr M.accRhsMptr) (a.fullyCollapse (tblOf PV)).2)) ∧
  -- .transcript : challenges in theta slots, commitments by region, evals spilled, q_eval cursor
  (Checkpoint.transcript ≤ k →
     holdsFr st (ptrAddr M.thetaMptr) S.trace.theta ∧ holdsFr st (ptrAddr M.betaMptr) S.trace.beta ∧
     holdsFr st (ptrAddr M.gammaMptr) S.trace.gamma ∧ holdsFr st (ptrAddr M.trashChallengeMptr) S.trace.trashChallenge ∧
     holdsFr st (ptrAddr M.yMptr) S.trace.y ∧ holdsFr st (ptrAddr M.xMptr) S.alg.x ∧
     holdsFr st (ptrAddr M.x1Mptr) S.a.x1 ∧ holdsFr st (ptrAddr M.x2Mptr) S.a.x2 ∧
     holdsFr st (ptrAddr M.x3Mptr) S.b.x3 ∧ holdsFr st (ptrAddr M.x4Mptr) S.c.x4 ∧   -- x3 already truncated (TranscriptProofParser.yul:365)
     holdsG1s E st (ptrAddr M.adviceCommsMptrBase) (S.trace.adviceCommitments.getD 0 #[]) ∧
     holdsG1s E st (ptrAddr M.quotientLimbCommsMptrBase) S.alg.quotientLimbComs ∧
     -- lookupM / permZ / lookupHelper / lookupZ / trashcan regions analogously, in ProofReadPlan order
     holdsG1 E st (ptrAddr M.fComMptr) S.b.fCom ∧ holdsG1 E st (ptrAddr M.piMptr) S.c.pi ∧
     holdsFrs st (ptrAddr M.reversedEvalsMptr) (reversedEvalsOf PV S) ∧   -- the plan's REVERSED_EVALS order (Data.new), owed bridge
     wordAt st (ptrAddr M.qEvalCptrMptr) = BitVec.ofNat 256 PV.proofLayout.qEvalCptr) ∧
  -- .lagrange : Lagrange.yul:81-86
  (Checkpoint.lagrange ≤ k →
     holdsFr st (ptrAddr M.xNMptr) S.alg.xn ∧ holdsFr st (ptrAddr M.lLastMptr) S.lLast ∧
     holdsFr st (ptrAddr M.lBlindMptr) S.lBlind ∧ holdsFr st (ptrAddr M.l0Mptr) S.l0 ∧
     holdsFr st (ptrAddr M.instanceEvalMptr) S.instanceEval) ∧
     -- X_N_MINUS_1_INV_MPTR: contract-only, no production consumer, no Lean counterpart: unconstrained
  -- .quotient : QuotientAndLinearization.yul:41, :125-126, SELECTOR_ACC buckets
  (Checkpoint.quotient ≤ k →
     holdsFr st (ptrAddr M.quotientEvalMptr) S.linCom.eval ∧
     holdsFrs st M.selectorAccMptr (selectorBucketsOf S.linCom) ∧
     holdsFr st (ptrAddr M.quotientMptr) S.alg.splittingFactor ∧
     holdsFr st (ptrAddr M.quotientMptr + 32) (1 - S.alg.xn)) ∧
  -- .pcs : Pcs block 4-6 outputs; PAIRING_LHS = π, PAIRING_RHS = final_com − v·G + x3·π (kzg/mod.rs:1838-1920)
  (Checkpoint.pcs ≤ k →
     holdsFr st (ptrAddr M.fEvalMptr) S.b.fEval ∧ holdsFr st (ptrAddr M.vMptr) S.c.v ∧
     holdsG1 E st (ptrAddr M.finalComMptr) S.c.finalCom.eval ∧
     holdsG1 E st (ptrAddr M.pairingLhsMptr) S.c.dual.left.eval ∧
     holdsG1 E st (ptrAddr M.pairingRhsMptr) S.c.dual.right.eval) ∧
  -- .pairing : the decision, in DualMSM orientation; FinalPairing rewrote the slots in acc mode
  (k = Checkpoint.pairing →
     VEnv.get V "success" = some 1 ∧
     (PV.hasAccumulator = false → DualMSM.check S.c.dual params = true))
```
hypotheses:
- Permanent-region scoping (D-P18, LayoutMemory.lean:909) - every slot named is in vk_payload, challenge_slots, the theta block (ThetaSlot.word 0..48 are inside the 52-word permanent window), q_eval_cptr_slot, decoded_evals or decompressed_commitments.
- selectorAccMptr is a Nat field (not Ptr) in VerifierMemoryLayout; the SELECTOR_ACC region is phase quotientVm scratch in the layout but is READ by PCS block 5 - if it is not permanent in LayoutMemory.new this clause must move to a phase-scoped side predicate (check `new` region list; flagged).
- PAIRING_LHS/RHS clause is correct at .pcs only (survey constraint on FinalPairing.yul:33-58 in-place rewrite).
non-vacuity: Swapping the pairingLhs/pairingRhs clauses makes finalPairing_spec false (the frame at AssemblyHelpers.yul:284-287 pairs scratch[0..0x80) with G2_BASE); dropping `st.halted = none` lets a reverted state satisfy Inv and cons_split could not discharge the revert arm; gate: Inv is satisfiable on a hand-built state (example) and refuted by perturbing one word.

### Midfall.Lowering.PartialSpecs (per-partial forall-runs contracts, sound and progress forms)  (obligation-field; statable-now over the abstract Surface (needs Bridge.Dialect/honestCalls/honestResponds from Bridge.lean; the structure form needs no proof hole); M5 (vkLoading, transcriptParser, lagrange), M6/M7 (quotientLin, pcs), pulled-forward (finalPairing, traceReturn)) — formal/Midfall/Lowering/Partials.lean
```lean
namespace Midfall.Lowering
open YulSemantics YulSemantics.EVM

/-- What a render exposes to the per-partial theorems: the constant-substituted
    block of each partial (no Lean renderer returns these yet, P-13) and the main
    block whose hoisted scope holds AssemblyHelpers (fail, scalar_inv, squeeze_to,
    batch_invert, ec_pairing, validate_public_accumulator). -/
structure Surface where
  main : Block Op
  blk : Partial → PlanView → Block Op

/-- A revert as the EVM state records it (EVMExec.lean:844-846). -/
def Reverted (st : EvmState) : Prop := ∃ d, st.halted = some (.revert, d)

/-- Permissive relation for soundness: any response the honest precompiles could
    not give must be a failure (gas is unmodelled, so failure is always allowed). -/
def Permissive (product : Midfall.Yul.PairingProduct) (calls : ExternalCalls) : Prop :=
  ∀ req st resp, calls.Call req st resp → resp.success = true →
    Bridge.honestResponds product req = some resp.returndata

abbrev Funs (S : Surface) (calls gas) := FunEnv (Bridge.Dialect calls gas)
def mainScope (S : Surface) (calls gas) (outer : Funs S calls gas) : Funs S calls gas :=
  hoist (Bridge.Dialect calls gas) S.main :: outer

/-- One partial, soundness shape: every run from Inv (pre) either reverts or
    continues normally into Inv (post). `extra` is the partial-specific conjunct. -/
def PartialSound (S : Surface) (E) (params) (q : Partial) (PV : PlanView) (Snap : Snapshot p G₁ G₂ Gₜ)
    (calls gas) (extra : VEnv (Bridge.Dialect calls gas) → EvmState → Prop) : Prop :=
  ∀ outer, StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer) (S.blk q PV)
    (fun V st => Inv E params q.pre PV Snap V st)
    (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
      (o = .normal ∧ Inv E params (q.pre.next) PV Snap V' st' ∧ extra V' st'))

/-- Progress shape under the functional honest relation: no revert. -/
def PartialProgress (S) (E) (params) (q) (PV) (Snap) (product) (gas) : Prop :=
  ∀ outer, StmtsContractAll (D := Bridge.Dialect (Bridge.honestCalls product) gas)
    (mainScope S _ gas outer) (S.blk q PV)
    (fun V st => Inv E params q.pre PV Snap V st)
    (fun _ _ V' st' o => o = .normal ∧ Inv E params q.pre.next PV Snap V' st')

/-- The per-partial obligations. Every field quantifies over the snapshot of the
    run (snapshotOf = .ok Snap), EnvAgrees, Supported.production, and the calldata
    hypothesis `hcd : st.env.calldata = cd.toList ∧ decodeCalldata PV cd = some (ms, instWords)`
    (decodeCalldata is the calldata area). -/
structure PartialSpecs (S : Surface) (E : VerifierEnv p G₁ G₂ Gₜ) (params) (sG2gen) (encG2) (product) : Prop where
  vkLoading_sound : ∀ PV vk inst ms Snap calls gas, Permissive product calls → EnvAgrees E vk PV params sG2gen encG2 →
    snapshotOf E H vk inst ms none = .ok Snap → PV.hasAccumulator = false →
    PartialSound S E params .vkLoading PV Snap calls gas (fun _ _ => True)
  transcriptParser_sound : … PartialSound S E params .transcriptParser PV Snap calls gas (fun _ _ => True)
  lagrange_sound : … PartialSound S E params .lagrange PV Snap calls gas (fun _ _ => Snap.alg.x ^ vk.domain.n ≠ 1)
    -- a normal exit PROVES xNotRoot (batch_invert rejected zero): the contract is stricter here
  quotientLin_sound : … ChallengesGood vk Snap → PartialSound S E params .quotientLin PV Snap calls gas (fun _ _ => True)
    -- without ChallengesGood.logupNoPanic the obligation is FALSE (contract normal, Lean panic)
  pcs_sound : … PartialSound S E params .pcs PV Snap calls gas (fun _ _ => True)
  finalPairing_sound : … Eip2537.Holds E encG2 product → PartialSound S E params .finalPairing PV Snap calls gas (fun V' _ => VEnv.get V' "success" = some 1)
  traceReturn_sound : … StmtsContractAll … (S.blk .traceReturn PV) (Inv … .pairing …)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue))
  -- progress twins (honest calls), each with the side condition that makes it true:
  vkLoading_progress : … PartialProgress …
  transcriptParser_progress : … PartialProgress …
  lagrange_progress : … ChallengesGood vk Snap → PartialProgress …
  quotientLin_progress : … PartialProgress …
  pcs_progress : … PartialProgress …
  finalPairing_progress : … Eip2537.Holds E encG2 product → DualMSM.check Snap.c.dual params = true → PartialProgress …
end Midfall.Lowering
```
hypotheses:
- Permissive calls (Y-1 soundness relation) - under relational externals the existential StmtsContract says nothing about all runs.
- hoisted funs = hoist S.main :: outer - BigStep callOk (:185-193) runs helpers with params ++ rets only, so fail/scalar_inv must be resolvable from the scope, not from the partial.
- snapshotOf = .ok Snap - the Snapshot is what Inv relates memory to; for soundness the theorem is stated for the Snap that exists, and verifier_sound derives its existence from the no-panic hypothesis.
- ChallengesGood - R-2 manifestations 1 and 2 as established above.
- Supported.production - trace renders return false instead of reverting (FinalPairing.yul:81-87, TraceReturn.yul:55-61).
- Eip2537.Holds - the pairing product is an oracle (Externals.lean:941).
non-vacuity: lagrange_sound's extra conjunct is falsified by a Lagrange block that skips the gp = 0 check (AssemblyHelpers.yul:226-229): a run with x = ω^i would exit normally with x^n = 1; traceReturn_sound fails for a trace render (returns 0 when success = 0).

### Midfall.Assumptions.Eip2537.Holds  (structure; statable-now; pulled-forward finalPairing_spec; M7) — formal/Midfall/Assumptions/Eip2537.lean
```lean
namespace Midfall.Assumptions
open Midfall.Halo2 Midfall.Yul
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- The EIP-2537 precompiles, as the verifier uses them, agree with the abstract
    pairing through the codecs. `encG2` is abstract: Common has no G2 codec; the
    generator embeds g2ToU256s ∘ codecs.g2Repr (Vk.lean:331, Encoding.lean:976). -/
structure Eip2537.Holds (E : VerifierEnv p G₁ G₂ Gₜ) (encG2 : G₂ → Bytes)
    (product : PairingProduct) : Prop where
  /-- toEip output passes common_uncompressed_g1 and the precompile decoders. -/
  g1Valid : ∀ Q : G₁, ∃ pt, g1Of? (E.g1.toEip Q) = some pt ∧ g1PointMsmValid pt = true
  g2Valid : ∀ R : G₂, ∃ pt, g2Of? (encG2 R) = some pt ∧ g2PointValid pt = true
  /-- PAIRING_CHECK on two pairs is the additive pairing equation (EIP: Π e(P_i,Q_i) = 1). -/
  pairing2 : ∀ (P₁ P₂ : G₁) (Q₁ Q₂ : G₂),
    product (pairingFrame [(E.g1.toEip P₁, encG2 Q₁), (E.g1.toEip P₂, encG2 Q₂)]) = true ↔
      P.e (Additive.ofMul P₁) (Additive.ofMul Q₁) + P.e (Additive.ofMul P₂) (Additive.ofMul Q₂) = 0
  /-- G1ADD (0x0b, 0x100-byte input, R-21). -/
  g1Add : ∀ P₁ P₂ : G₁,
    g1AddOutput (ByteArray.append (E.g1.toEip P₁) (E.g1.toEip P₂)) = some (E.g1.toEip (P₁ * P₂))
  /-- One-pair G1MSM (0x0c, interleaved 0xa0-byte records, R-21). -/
  g1Msm1 : ∀ (Q : G₁) (s : Fr p),
    g1MsmOutput (g1MsmFrame [(E.g1.toEip Q, wordToBytesBE (frWord s))]) = some (E.g1.toEip (gsmul s Q))
  /-- Soundness side: a frame the precompile accepts decodes to a group element. -/
  g1Decodes : ∀ b : Bytes, (∃ pt, g1Of? b = some pt ∧ g1PointMsmValid pt = true) → ∃ Q, E.g1.toEip Q = b
end Midfall.Assumptions
```
hypotheses:
- This IS the hypothesis structure (gap policy: unproven precompile semantics become a named hypothesis in Assumptions/). PairingProduct is the arithmetic hole (Externals.lean:934-941).
- g1Decodes is what closes the points_subgroup_checked gap for the no-acc path: the parser absorbs raw calldata bytes and only G1MSM/pairing validate them.
non-vacuity: With product := fun _ => true, pairing2 fails at P₁ = P₂ = P.g₁, Q₁ = P.g₂, Q₂ = P.g₂ versus Q₂ = P.g₂⁻¹ (one side zero, the other e(g₁,g₂)+e(g₁,g₂)); with g1Msm1 stated over the scalar `s` instead of `frWord s` the frame would carry a non-canonical word and the clause would be false for s with s.val ≥ 2^128 under truncation - the gate example exhibits both.

### Midfall.Halo2.Spec.PairingLift.exists_zmod_smul_generator  (lemma-provable-now; provable-now; Phase 4a algebra (now)) — formal/Midfall/Halo2/Spec/PairingLift.lean
```lean
namespace Midfall.Halo2.Spec.PairingLift
variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)] [P : AdmissiblePairing G₁ G₂ Gₜ]

/-- The ZMod p action is the integer action: (k : ZMod p) • a = k • a. -/
theorem zmod_smul_eq_zsmul (k : ℤ) (a : Additive G₁) : ((k : ZMod p) • a) = k • a :=
  Int.cast_smul_eq_zsmul (ZMod p) k a   -- name to confirm with #check

/-- Every element of a prime-order group is a power of any non-identity element:
    G₁ is cyclic (isCyclic_of_prime_card PrimeOrderWith.hCard) and orderOf P.g₁ = p
    (orderOf_eq_prime_iff: g₁ ^ p = 1 by pow_card_eq_one, g₁ ≠ 1 by P.hG₁). -/
theorem exists_zmod_smul_generator (Q : G₁) : ∃ s : ZMod p, Q = gsmul s P.g₁ := by
  sorry

/-- Same for G₂ (used for sG2Prepared = s • g₂). -/
theorem exists_zmod_smul_generator₂ (R : G₂) : ∃ s : ZMod p, R = Additive.toMul (s • Additive.ofMul P.g₂) := by
  sorry
end Midfall.Halo2.Spec.PairingLift
```
hypotheses:
- PrimeOrderWith G₁ p (Nat.card G₁ = p) and P.hG₁ - both exist (ArkLib PrimeOrder.lean:40, Curve.lean:48). The critic lists this lemma as owed (unmentioned constraint on lifting pairing_reorder).
- Module (ZMod p) (Additive G₁) agrees with zpow - follows from Int.cast_smul_eq_zsmul; no extra hypothesis.
non-vacuity: False without hG₁ (take P.g₁ = 1 in a nontrivial group): the proof must use P.hG₁; a KAT over ZMod 17 as Additive (Multiplicative (ZMod 17)) with generator 3 exhibits a concrete witness s for Q = 5.

### Midfall.Halo2.Spec.PairingLift.DualMSM_check_iff_rustEq / pairingFrame_iff_contractEq / finalPairing_check_bridge  (lemma-provable-now; provable-now; Phase 4a algebra (now); consumed by the pulled-forward finalPairing_spec) — formal/Midfall/Halo2/Spec/PairingLift.lean
```lean
/-- DualMSM.check in exponents. `left = xL·g₁`, `right = xR·g₁`, sG2Prepared = s·g₂,
    nG2Prepared = g₂⁻¹ (R-4). Unfolds Msm.lean:222-233: decideBool (P.decEqGₜ …) = true ↔
    e(left, s·g₂) + e(right, g₂⁻¹) = 0 ↔ (xL·s − xR) • e(g₁,g₂) = 0 ↔ rustEq xL xR s,
    using LinearMap.map_smul, map_neg, hNonDeg and smul_eq_zero over the field ZMod p. -/
theorem DualMSM_check_iff_rustEq (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (xL xR s : Fr p)
    (hL : g.left.eval = gsmul xL P.g₁) (hR : g.right.eval = gsmul xR P.g₁)
    (hs : params.sG2Prepared = Additive.toMul (s • Additive.ofMul P.g₂))
    (hn : params.nG2Prepared = P.g₂⁻¹) :
    DualMSM.check g params = true ↔ Spec.Lemmas.rustEq xL xR s := by
  sorry

/-- The contract frame at FinalPairing.yul:88 via AssemblyHelpers.yul:284-287:
    [PAIRING_RHS | G2_BASE | PAIRING_LHS | NEG_S_G2_BASE] - the SWAP is at the call
    site, the layout is caller-ordered. -/
theorem pairingFrame_iff_contractEq (hH : Midfall.Assumptions.Eip2537.Holds E encG2 product)
    (left right : G₁) (sG2gen : G₂) (xL xR s : Fr p)
    (hL : left = gsmul xL P.g₁) (hR : right = gsmul xR P.g₁)
    (hs : sG2gen = Additive.toMul (s • Additive.ofMul P.g₂)) :
    product (Midfall.Yul.pairingFrame
      [(E.g1.toEip right, encG2 P.g₂), (E.g1.toEip left, encG2 sG2gen⁻¹)]) = true ↔
    Spec.Lemmas.contractEq xL xR s := by
  sorry

/-- The bridge finalPairing_spec consumes: Lean decision = contract decision. -/
theorem finalPairing_check_bridge (hH : Midfall.Assumptions.Eip2537.Holds E encG2 product)
    (g : DualMSM (Fr p) G₁ G₂ Gₜ) (params) (sG2gen : G₂)
    (hn : params.nG2Prepared = P.g₂⁻¹) (hsg : params.sG2Prepared = sG2gen) :
    DualMSM.check g params = true ↔
    product (Midfall.Yul.pairingFrame
      [(E.g1.toEip g.right.eval, encG2 P.g₂), (E.g1.toEip g.left.eval, encG2 sG2gen⁻¹)]) = true := by
  obtain ⟨xL, hL⟩ := exists_zmod_smul_generator (P := P) g.left.eval
  obtain ⟨xR, hR⟩ := exists_zmod_smul_generator (P := P) g.right.eval
  obtain ⟨s, hs⟩ := exists_zmod_smul_generator₂ (P := P) sG2gen
  rw [DualMSM_check_iff_rustEq g params xL xR s hL hR (hsg ▸ hs) hn,
      pairingFrame_iff_contractEq hH _ _ sG2gen xL xR s hL hR hs]
  exact Spec.Lemmas.pairing_reorder xL xR s
```
hypotheses:
- hn (R-4: nG2Prepared differs between ofParams and read); hsg (sG2Prepared vs ParamsKZG.sG2, critic) - without them the Lean check and the contract frame use different G2 points.
- Eip2537.Holds.pairing2 - the oracle must be the pairing.
- exists_zmod_smul_generator - the critic's owed lemma; what makes the exponent-level pairing_reorder applicable.
non-vacuity: Stating the frame as [(left, g₂), (right, sG2⁻¹)] (the stale Spec/Lemmas.lean:19-20 order) breaks finalPairing_check_bridge: it would require e(left,g₂)+e(right,(s g₂)⁻¹) = 0 ↔ xL·s − xR = 0, i.e. xL − s·xR = 0, false for xL = 1, xR = 1, s = 2 over ZMod 17 (example to include).

### finalPairing_spec (full: no-accumulator arm, progress twin, accumulator arm)  (theorem-sorry; needs P-BR Bridge.lean (Dialect/honestCalls/honestResponds) and the AssemblyHelpers.yul + FinalPairing.yul partial ASTs (P-13) to be more than a Surface field; the statement is writable now over the abstract Surface; pulled forward: right after Bridge + Phase-4a (PLAN 14.4)) — formal/Midfall/Lowering/Partials.lean
```lean
/-- The ec_pairing frame [RHS|G2_BASE|LHS|NEG_S_G2] (AssemblyHelpers.yul:283-287) built by
    `ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)` (FinalPairing.yul:88) decides
    exactly DualMSM.check, through finalPairing_check_bridge. Production only:
    `if iszero(success) fail(ERR_PRECOMPILE_FAILED)` (:86), `if iszero(ret) fail(ERR_PRECOMPILE_FAILED)`
    (AH:296), `if iszero(ret) fail(ERR_PROOF_REJECTED); ret := 1` (AH:307-308). -/
theorem finalPairing_sound_noAcc (S : Surface) (E) (params) (sG2gen) (encG2) (product)
    (PV : PlanView) (vk) (Snap : Snapshot p G₁ G₂ Gₜ) (calls gas)
    (hperm : Permissive product calls) (hH : Midfall.Assumptions.Eip2537.Holds E encG2 product)
    (henv : EnvAgrees E vk PV params sG2gen encG2) (hacc : PV.hasAccumulator = false)
    (hprod : S.blk .finalPairing PV = finalPairingProductionBlock PV) :
    ∀ outer, StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer) (S.blk .finalPairing PV)
      (fun V st => Inv E params .pcs PV Snap V st)
      (fun _ _ V' st' o =>
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "success" = some 1 ∧
           DualMSM.check Snap.c.dual params = true ∧ Inv E params .pairing PV Snap V' st')) := by
  sorry

theorem finalPairing_progress_noAcc … (hcheck : DualMSM.check Snap.c.dual params = true)
    (hsucc : ∀ V st, Inv E params .pcs PV Snap V st → VEnv.get V "success" = some 1) :
    ∀ outer, StmtsContractAll (D := Bridge.Dialect (Bridge.honestCalls product) gas) …
      (fun V st => Inv E params .pcs PV Snap V st)
      (fun _ _ V' st' o => o = .normal ∧ Inv E params .pairing PV Snap V' st') := by
  sorry

/-- Accumulator arm (FinalPairing.yul:14-61 then :88). The batch preimage is
    tag ‖ VK_DIGEST ‖ RHS ‖ LHS ‖ ACC_RHS ‖ ACC_LHS (0x240 bytes at 0x1000), alpha =
    keccak mod r with 0 ↦ 1, exactly alphaOf (Accumulator.lean:1014-1021); the slots are
    rewritten in place to RHS + α·ACC_RHS and LHS + α·ACC_LHS via G1MSM+G1ADD, so the
    decision is batchedCheck in DualMSM orientation (Accumulator.lean:1036-1045). -/
theorem finalPairing_sound_acc … (henc : PV.hasAccumulator = true)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (hS : Snap.acc = some a) (tbl := tblOf PV)
    (hkec : ∀ V st, Inv E params .pcs PV Snap V st →
       st.env.keccakOf = fun l => H (ByteArray.mk l.toArray)) :
    ∀ outer, StmtsContractAll … (S.blk .finalPairing PV)
      (fun V st => Inv E params .pcs PV Snap V st)
      (fun _ _ V' st' o =>
        (o = .halt ∧ Reverted st') ∨
        (o = .normal ∧ VEnv.get V' "success" = some 1 ∧
           batchedCheck params
             (alphaOf (p := p) H (frWord vk.transcriptRepr) E.g1
               Snap.c.dual.left.eval Snap.c.dual.right.eval
               (a.fullyCollapse tbl).1 (a.fullyCollapse tbl).2)
             Snap.c.dual a tbl = true)) := by
  sorry
```
hypotheses:
- Eip2537.Holds - pairing2 for the decision; g1Msm1/g1Add for the acc rewrite (FinalPairing.yul:39,44,53,58).
- EnvAgrees.nG2/sG2/g2BaseWords/negSG2Words - the G2 bytes mcopied from the VK payload (AH:285,287) must be encG2 P.g₂ and encG2 sG2gen⁻¹.
- Permissive / honestCalls - as in every partial; a failed staticcall reverts PrecompileFailed (MF-4), which the revert arm absorbs.
- hprod (production block) - trace render returns iszero(iszero(ret)) and never reverts.
- hkec - alphaOf is hash-parametric; the EVM hashes through env.keccakOf (Y-2), installed by withKeccak.
- Inv .pcs pre, not a bare RunContract - the pairing block reads memory written by Pcs; PLAN's `RunContract (blk …) (Inv .start)` form has the wrong arity and the existential semantics (survey).
non-vacuity: Replacing the frame by the unswapped order makes the sound conclusion false on any proof with left ≠ right scaled consistently (example in PairingLift); dropping the `success = 1` conjunct lets a trace render satisfy the post; the acc arm with alphaOf argument order (accLhs accRhs) swapped fails against FinalPairing.yul:25-26 (ACC_RHS before ACC_LHS in the preimage) - checked by the alphaOf preimage KAT.

### Midfall.Lowering.abiTrue / traceReturn_spec  (theorem-sorry; statable-now over Surface; pulled forward with finalPairing) — formal/Midfall/Lowering/Partials.lean
```lean
/-- The 32-byte BE word 1 the production TraceReturn returns:
    mstore(RETURN_MPTR, 1); return(RETURN_MPTR, 0x20) with RETURN_MPTR =
    verifierReturnMptr = 0x1000 (TraceReturn.yul:70-72, Layout.lean:734). -/
def abiTrue : List UInt8 := (wordToBytesBE 1).toList

theorem traceReturn_spec (S : Surface) … (PV) (Snap) (calls gas)
    (hprod : S.blk .traceReturn PV = traceReturnProductionBlock PV) :
    ∀ outer, StmtsContractAll (D := Bridge.Dialect calls gas) (mainScope S calls gas outer) (S.blk .traceReturn PV)
      (fun V st => Inv E params .pairing PV Snap V st)
      (fun _ _ _ st' o => o = .halt ∧ st'.halted = some (.ret, abiTrue)) := by
  sorry
```
hypotheses:
- Inv .pairing gives success = 1 (so `if iszero(success) fail(ERR_PROOF_REJECTED)` is not taken) and st.halted = none.
- Production render (TraceReturn.yul:55-61 returns iszero(iszero(success)) in trace mode).
non-vacuity: A block that returned (RETURN_MPTR, 0x40) or returned success itself (trace) fails the exact `some (.ret, abiTrue)`; the return opcode records readBytes memory p s in halted (EVMExec.lean:840-843).

### verifier_sound / lowering_equivalence completeness as PLAN writes them  (theorem-sorry; FALSE-as-planned (both conjuncts, for all H); statable with hnopanic/hgood; M7) — formal/docs/PLAN.md:456-487 (to be restated in Midfall/Lowering/Obligations.lean)
```lean
-- PLAN form: verifier_sound (hrun : RunVerifier H L W cd mem₀ obs) (hret : obs.isReturn) :
--   obs.data = abiTrue ∧ LeanAccepts H g L cd
-- Restated with the side condition this scope established (both directions need one):
theorem verifier_sound … (hnopanic : ∀ site, snapshotOf E H vk inst ms acc ≠ .error (Fault.panic site))
    (hrun : Bridge.Run … obs) (hret : obs.isReturn) : obs.data = abiTrue ∧ LeanAccepts H g L cd
theorem verifier_complete … (hgood : ∃ Snap, snapshotOf E H vk inst ms acc = .ok Snap ∧ ChallengesGood vk Snap)
    (hacc : LeanAccepts H g L cd) : ∀ obs, RunShell … (honestCalls) obs → obs = .return abiTrue
```
hypotheses:
- hnopanic - NEW: the logup prefix/suffix divergence; without it there is an H (x on the bad set) for which the contract returns true and verifyMsgs = .error (Fault.panic "proofs/src/plonk/logup.rs:460").
- hgood - R-2 first manifestation (x^n = 1): contract reverts, Lean accepts.
non-vacuity: Counterexample to the unconditioned PLAN soundness: one lookup with input chunk of size k ≥ 2 (Logup.lean:279 inverts only when k ≥ 1 - also the k = 1 inline path never inverts), honest proof, H chosen so that x makes compressed(f_1)(x) + β = 0; the contract evaluates h·0 − Π_{j≠1}(f_j+β) which the honest helper identity satisfies, returns 1; Lean panics. Counterexample to unconditioned completeness: x = ω^j outside the rotation window (critic).

### Midfall.Lowering.ContractRefAcceptsAcc (accumulator arm of ContractRef.accepts)  (def; statable-now (toExec is a 4-line def; decodeAcc has no olean - run #check first per critic); M7 / contractRef_acc_complete) — formal/Midfall/Lowering/Surface.lean
```lean
/-- PLAN 9.5 ContractRef.accepts, accumulator arm, over the Exec encoding via toExec
    (D-P16) with the fixed-base TABLE as a parameter (Midfall.Halo2.fixedBases inserts
    "-G" ↦ (1 : G₁)⁻¹ = identity, a defect: use fb from the generator). Argument
    order of alphaOf is (kzgLhs kzgRhs accLhs accRhs); the hashed order is RHS then LHS. -/
def ContractRefAcceptsAcc (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂)
    (vk : VerifyingKey (Fr p) G₁) (enc : Midfall.Generator.AccumulatorEncoding)
    (fb : Array (AccFixedBase G₁)) (inst : Array (Fr p)) (ms : List (Msg (Fr p) G₁)) : Bool :=
  match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
  | .error _ => false
  | .ok d =>
    let tbl := fb.map (fun b => (b.name, b.base))
    match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb (inst.map frWord) with
    | none => false
    | some a =>
      let (aL, aR) := a.fullyCollapse tbl
      batchedCheck params (alphaOf (p := p) H (frWord vk.transcriptRepr) E.g1 d.left.eval d.right.eval aL aR) d a tbl
```
hypotheses:
- None (definition); its correctness target is finalPairing_sound_acc.
non-vacuity: Passing `fixedBases vkName …` instead of fb makes fromDualMsm/fullyCollapse use base 1 for "-G", so the −v·G term vanishes and every acc proof with v ≠ 0 would be mis-decided; the KAT with a two-element fb exhibits different Bools.

### pcs_spec PAIRING_LHS/RHS clause placement  (theorem-sorry; FALSE-as-planned at .pairing in acc mode; correct at .pcs; M7) — formal/Midfall/Lowering/Inv.lean
```lean
-- Inv .pcs: holdsG1 pairingLhs Snap.c.dual.left.eval ∧ holdsG1 pairingRhs Snap.c.dual.right.eval
-- Inv .pairing: NO such clause in accumulator renders (FinalPairing.yul:33-58 rewrites both
-- slots in place to RHS + α·ACC_RHS and LHS + α·ACC_LHS before :88).
```
hypotheses:
- Survey constraint (Generator render area): the PLAN comment places the equality after FinalPairing.
non-vacuity: If the clause were kept at .pairing in acc mode, finalPairing_sound_acc could not be proved (the slots hold batched points), and pcs_spec would be stated about a dead value.


# DESIGN 2: Yul bridge + headline theorems. Ground truth: survey.md/critic.md plus direct reads of vendor EVMExec/BigStep/Contract/Observation/Determinism, Midfall/Yul/Externals.lean, Lowering/{Types,SemanticEquivalence}.lean, Statements.lean, Exec/{Native,Accumulator,Msm,Params,Logup,Verifier,MultiOpen,Transcript}.lean, Generator/{Api,Vk,Models,Layout,Abi}.lean, the templates (FinalPairing/AssemblyHelpers/Lagrange/VkLoading/TraceReturn/QuotientAndLinearization/AccumulatorHelpers.yul, Halo2Verifier.sol, Halo2QuotientEvaluator.sol), quotient.rs structured_lookup_loop_block and yul_emit.rs lookup_computations, logup.rs:400-480, design.md D-P10/13/15/16/18/20, REVIEW R-2/R-10/R-11/R-26/R-35/R-42, PLAN 9.5/10/11/14. Everything below is typed over objects that exist today; unported pieces are fields of one Surface record. NEW FINDING (task item C, checked): the contract's logup helper constraint is computed WITHOUT inversion on both Yul paths (yul_emit.rs:439-560 prefix/suffix products; quotient.rs:1688-1880 same, k=1 arm emits h*(f+beta)-1), so at f_j(x)+beta = 0 the contract computes a definite value and continues while Lean/Rust abort (Logup.lean:279 Fault.panic logup.rs:460). Soundness as PLAN writes it therefore has a candidate counterexample and needs an explicit NoLogupPanic hypothesis (stated operationally, no snapshot needed). Completeness needs x^n != 1 via an xOf squeeze replay (Lagrange.yul:93-99 reverts, Lean accepts). x3 in a point set is consistent (both sides fail: scalar_inv reverts, Lean panics).

## files
### formal/Midfall/Yul/Bridge.lean
Open-dialect run layer (D-P10/P-BR): Bridge.Dialect/Run/RunCommitted over EVM.evmWithExternal calls ExternalCreates.none gas; Functional predicates; per-op determinism; Run.det/RunCommitted.det with a two-response counterexample gate; keccak hook (hashOfBytes/withKeccak) plus keccakOf invariance along Step; Obs/ObsView/isReturn/returnData/isRevertOrHalt/worldUnchanged/abiTrue; Externals->EVM conversions (toYulReq, ofOutcome, failResp, 160-bit target hit); honestCalls and permissiveCalls folds of honestRelations plus an evaluator slot; Evaluator.rel running a runtime block under the closed dialect; forall-runs contracts RunContractAll/StmtsContractAll and the composition lemmas the vendor lacks (halting-head cons, append, cond, switch, call, halting loop).
imports: YulSemantics, YulSemantics.Dialect.EVM, YulSemantics.Contract, YulSemantics.Observation, YulSemantics.Object, YulSemantics.ObjectRun, Midfall.Common.Bytes, Midfall.Common.Keccak, Midfall.Yul.Externals
hazards:
- Never write YulSemantics.RunCommitted here (closed dialect, Y-3): every Run must name (D := Bridge.Dialect c g) because Dialect.Op is a structure field and is not inferable from Block Op
- ExternalGas.any breaks Run.det: soundness quantifies over all g, completeness/determinism use ExternalGas.ofFun
- Externals.accepts compares the full 256-bit target; the EVM aliases on accountKey (mod 2^160): the fold must compare accountKey, and the address-disjointness lemma must be about keys
- Midfall.Yul.modexpFrameBytes vs Midfall.Generator.modexpFrameBytes name clash: do not open Midfall.Generator here
- Externals.lean has zero theorems; its KATs are #eval Bool and cannot be cited as lemmas (relationKats_ok distinctness must be re-proved by norm_num on the four literals)
- This file must stay free of Midfall.Halo2.Exec imports so the Yul layer does not depend on L0; Hash = Bytes -> H256 is written out as that type
- No Instances/ import (D-P17); if a non-vacuity run example is wanted, build Step derivations by hand or use a #eval Bool over Interp.run with a new lawful ExecDialect
### formal/Midfall/Lowering/Surface.lean
One Prop-free record bundling every unported object PLAN 9.5 names, typed over existing types: the verifier environment (E, params, vk, cfg : GeneratorConfig, accFixedBases : Array (AccFixedBase G1), vkDigest word), the lowered program (L : Lowered extended with bindLocals block, shell object, irRuntime accessor, evaluator runtime block + Layout), the codecs (repackProof, encodeCalldata, decodeCalldata over raw Word256 instances), render/lower/print/astOfMain for the structural render_eq_print, irCheck, the Supported and Deployment predicates, Checkpoint/Snapshot/Inv API, blk : Partial -> Block Op, toExec and instOfWords?. Also hosts ContractRefAcceptsAcc (accumulator arm, table passed in) and LeanAccepts.
imports: Midfall.Yul.Bridge, Midfall.Lowering.Types, Midfall.Halo2.Exec.Native, Midfall.Halo2.Exec.Accumulator, Midfall.Generator.Api, Midfall.Generator.Layout, Midfall.Generator.Models, Midfall.Generator.Abi, Midfall.Generator.Quotient.VmTypes
hazards:
- Do NOT import Midfall.Generator.Vk (it imports Instances.ExponentModel; the CI gate checks direct imports only, but #print axioms would show the model in scope) - the vk_digest link is a hypothesis field vkDigest_spec instead
- Two AccumulatorEncoding types in scope once Midfall.Halo2 and Midfall.Generator are open: always fully qualify; toExec maps Generator -> Halo2
- decodeAcc, KzgAcc.* need (p := p) (G₂ := G₂) (Gₜ := Gₜ); prepareMsgs/verifyMsgs need (Gₜ := Gₜ)
- Statements.lean is SHA-pinned: nothing here may redeclare verifyNative_iff_msgs/verifyMsgs_iff_spec/contractRef_noAcc or live in namespace Midfall.Statements
- decodeAcc's `-s` at Accumulator.lean:987 has never been compiled (no .olean): run #check @Midfall.Halo2.decodeAcc before building on it
- Lowering/Types.lean's Deployment/Supported names are taken: use DeploymentW / SupportedS or shadow inside a new namespace Midfall.Lowering.Surface
### formal/Midfall/Lowering/Obligations.lean
The statements. (1) structure LoweringCorrect (S : Surface ...) : Prop with fields verifier_sound, verifier_complete, only_two_outcomes, ir_refines, end_to_end_noAcc, render_eq_print, finalPairing_spec, traceReturn_spec (everything that depends on unported pieces; no proof holes). (2) plain theorems provable now: lowering_equivalence (from the fields), lowering_equivalence_noAcc, contractRef_noAcc_of_semanticEquivalence, instOfWords_of_decode, permissive_of_honest, Bridge determinism corollaries. (3) plain theorems with registered holes: contractRef_acc_complete, batched_complete, batched_atMostOneRoot, dualMsm_check_reorder (pairing_reorder lifted to DualMSM.check), verifyNative_iff_msgs_codec (restated with E.g1.compressedRoundtrip), modexpInv_correct.
imports: Midfall.Lowering.Surface, Midfall.Lowering.SemanticEquivalence, Midfall.Assumptions.Precompiles, Midfall.Assumptions.Codec, Midfall.Halo2.Spec.Lemmas
hazards:
- Doc comments must not spell the s-word (lean_grep.py counts it inside /-- -/ after a primed identifier such as h' trips in_char mode); write 'proof hole'
- All `by sorry` lines must sit in one digit band (e.g. all three-digit lines 100-999) or checks.sh's lexicographic-vs-numeric sort mismatch fails the register; regenerate SORRY.md with scripts/gen_sorry.sh and add an owner() arm for the new file
- Register the file in Midfall.lean or check_orphans.py fails CI
- autoImplicit = false: every binder explicit; the variable block must match Statements.lean:29-34 including [P : AdmissiblePairing G₁ G₂ Gₜ]
- Do not use P.decEqG₁ as an instance implicitly; write haveI := P.decEqG₁ where DecidableEq G₁ is needed (D-P7)
### formal/Midfall/Assumptions/Precompiles.lean
Named hypothesis structures Eip2537.Holds (relating Externals.PairingProduct, g1AddOutput, g1MsmOutput and the byte validity predicates to AdmissiblePairing.e, the group law and scalar action through G1Codec.toEip and an abstract G2 encoder), the G2Enc record (the only G2 encoding in the tree is Generator.VkPointCodecs.g2Repr ∘ g2ToU256s, which lives behind Vk.lean's Instances import, so Precompiles takes an abstract toEipG2 : G₂ -> Bytes plus a hypothesis field tying it to the VK header words), and Modexp.Holds as a THEOREM target (modexpOutput is computed; its correctness is provable from modPow, not assumed).
imports: Midfall.Common.Curve, Midfall.Common.Codec, Midfall.Common.Bytes, Midfall.Yul.Externals, Midfall.Assumptions.Pairing, Midfall.Halo2.Exec.Kzg.Msm
hazards:
- No in-tree AdmissiblePairing instance can satisfy Eip2537.Holds (the exponent model's toEip is not a curve point); consistency of the hypothesis cannot be shown in Lean today - say so in the header
- The pairing frame is caller-ordered; the R-11 swap is at FinalPairing.yul:88, not in pairingFrame, so Holds must be stated over the frame as laid out ([lhs|G2|rhs|NEG_S_G2]) and the orientation handled in finalPairing_spec
- Must not import Instances/ (D-P17): a theorem-bearing file
### formal/Midfall/Assumptions/Codec.lean
G1Codec laws as one named hypothesis structure G1Codec.Laws (compressedRoundtrip, eipRoundtrip, eipWidth, compressedWidth, identityEip (toEip 1 = 128 zero bytes and ofEip? zeros = some 1), eipDecodeOfValid (every byte string Externals' g1Of?/g1PointMsmValid accepts decodes), encoderFirstEip restricted to the image) plus the provable Fr repr round trip frOfRepr?_frToRepr.
imports: Midfall.Common.Codec, Midfall.Common.Bytes, Midfall.Yul.Externals
hazards:
- eipRoundtrip in Codec.lean is decoder-first by design (R-34); the encoder-first law is restricted to canonical values and must not be stated over junk representations
- Instances/Bls12_381.lean has no torsion check, so the subgroup clause of eipDecodeOfValid is an obligation against the real codec, not a fact
### formal/Midfall/Assumptions/TwoAdicity.lean
P-4a FieldConsts.IsWellFormed (root_order, numBits_gt_s, numBits_bytes : divCeil (divCeil numBits 8) 2 = 16) and the vk.domain facts lagrange_spec needs (n = 2^k, barycentricWeight = n⁻¹, omegaInv*omega = 1, omega^n = 1). Owned by the Lagrange perspective; listed because verifier_complete's GenericX hypothesis and the critic's zeta_order finding interact with it.
imports: Midfall.Halo2.Exec.Arith, Midfall.Halo2.Exec.Domain, Mathlib.GroupTheory.OrderOfElement
hazards:
- zeta_order : orderOf fc.zeta = 3 cannot be discharged for fc17 (ZMod 17 has no element of order 3, Domain.lean:304-307): drop the field or switch the test field to one with 3 | p-1 (e.g. ZMod 7 or ZMod 13)
- Verifier path reads only numBits (truncate); rootOfUnity/zeta are read only by EvaluationDomain.new which the verifier never calls - so IsWellFormed is a Spec-layer prerequisite, not a per-partial one

## disagreements
- A (Bridge.Dialect fixed gas): keep the gas oracle a PARAMETER of Run/RunCommitted and quantify over all of it in soundness; use ExternalGas.ofFun only where determinism is needed (completeness `∀ obs`, RunCommitted.det). Soundness under `.ofFun` only would be weaker than the EVM.
- A (ContractRefAcceptsAcc signature): the accumulator arm must take the raw `instW : Array Word256` AND derive inst via instOfWords? internally; passing `inst : Array (Fr p)` and lifting through frWord loses the ≥ r rejection (R-26.7), and decodeAcc needs the raw words anyway.
- B (verifyNative_iff_msgs false for a degenerate codec): confirmed; additionally the restatement needs `p ≤ 2^256` for the Fr repr round trip, not only compressedRoundtrip. verifyMsgs_iff_spec: Spec.accepts also ignores E.delta and E.field.numBits (truncation), so an E-free spec cannot be equivalent even once Gₜ is threaded.
- C (logup f_j(x)+β = 0): CHECKED - the contract does NOT revert. Both Yul paths (yul_emit.rs lookup_computations, quotient.rs structured_lookup_loop_block) compute Σ_j ∏_{k≠j} via prefix/suffix products; the k = 1 arm emits `h*(f+β) - 1`. So at a zero denominator the contract computes a definite value and continues while Lean aborts (Fault.panic logup.rs:460). Soundness therefore needs the explicit NoLogupPanic hypothesis (stated operationally, no snapshot); I reject weakening the conclusion to `LeanAccepts ∨ LeanPanics`, which would hide the gap. Whether an adversary can turn this into an on-chain accept is a separate S-level question (the helper evaluation h(x) is bound by KZG), but the equivalence statement is false without the hypothesis.
- PLAN's end_to_end_noAcc RHS (`∀ obs, RunContractIR … → obs = .return abiTrue`) is satisfied vacuously when no run exists, so the ← direction is unprovable; the RHS must carry `∃ obs, RunContractIR …` as well. Same for verifier_complete, which PLAN already has in the ∃/∀ pair form.
- PLAN's `obs = .return abiTrue` cannot be a state equality: IR and shell differ in memory and VEnv. ObsEquiv and all headline conclusions must be at the ObsView level (outcome, halted, world components).
- D (Modexp.Holds): not a hypothesis. Externals.modexpOutput is computed, so the inversion frame's correctness is a theorem (modexpInv_correct) from modPow and Fermat; only availability/gas is modelled, and that is absorbed by the permissive relation.
- D (Eip2537.Holds must be over an abstract G2 encoder): the only G2 encoding is in Generator/Vk.lean behind the Instances import; Precompiles.lean cannot import it in a theorem file, so finalPairing_spec takes the G2_BASE/NEG_S_G2 bytes as Surface data with the g2Repr link as a hypothesis field.
- D (order): finalPairing_spec also needs dualMsm_check_reorder (bilinearity + exists_smul_eq from PrimeOrderWith) and MSMKZG.eval lemmas BEFORE the Yul block proof; those are Phase-4a algebra not yet in Spec/Lemmas.lean and should be scheduled with Bridge, not after.
- Hash-agnosticism (PLAN 10.3): achievable at the env level (Y-2), but only with DeploymentW.vkHash stated as `H vkRuntime = expectedVkCodehash` - for separate-VK renders the contract compares extcodehash (= H of the code) against a generation-time keccak constant, so for any H disagreeing with keccak256 on vkRuntime the contract reverts VkMismatch while Lean accepts. The ∀H statement is therefore true only on the H that agree with keccak256 at two byte strings; embedded-VK renders have no such constraint.
- worldUnchanged: the orchestrator's 'over world components' is right, but proving it for adversarial `calls` needs responses with world = CallWorld.ofState st (built into `permissive`) AND a NoWriters predicate on the program (fuel-based, R-37); Supported.production is what makes the generated blocks NoWriters. Alternative is a static-bit entry assumption - flagged as an open decision rather than chosen silently.

## open decisions
- Soundness side condition for item C: add NoLogupPanic as an explicit hypothesis (recommended; keeps the Lean port line-faithful and the gap visible) vs weakening the conclusion to `LeanAccepts ∨ Lean faults at logup.rs:460` vs a generator change to make the contract revert at a zero denominator (baseline bump). Recommended: hypothesis, plus an S-level follow-up on whether the contract's definite value is exploitable.
- worldUnchanged proof route: fuel-based syntactic NoWriters on the generated blocks (recommended; needs Supported.production) vs assuming a STATICCALL entry (st0.env.static = true), which is cheaper but models only eth_call/STATICCALL callers.
- Hash-agnosticism scope: accept that ∀H headline theorems hold only for H agreeing with keccak256 on vkRuntime/quotientRuntime (DeploymentW.vkHash as `H code = constant`), or restrict the ∀H claim to embedded-VK/inline-quotient renders. Recommended: keep DeploymentW as written and record the restriction in PLAN 10.3.
- D-P18 Supported.layout reading: option 1 (`memory.map.WellFormed ∧ memory.validate = .ok ()`) recommended; the Surface field is left as a Prop so either reading can be plugged in without restating theorems.
- Re-pin of Statements.lean to fill contractRef_noAcc from contractRefAccepts_iff_verifyMsgs (requires committing SemanticEquivalence.lean first). Recommended: re-pin once, together with any re-statement of verifyNative_iff_msgs (codec hypothesis) and verifyMsgs_iff_spec (E-dependent spec).
- Fix Midfall.Halo2.fixedBases' "-G" entry (identity instead of the negated generator; needs the generator, so the signature gains [AdmissiblePairing] or a `gen : G₁` argument) vs keep taking the table as a parameter everywhere. Recommended: fix the def (it is a port defect, R-class) and keep the parameter in ContractRefAcceptsAcc, since the contract table is positive-base anyway.
- Register policy for the new theorem file: keep all `by sorry` lines in one digit band (recommended short-term) vs fix checks.sh to sort `listed` numerically (correct fix, touches CI script).
- R-25 accWords meaning (identity-flagged coordinates projected to (0,0,1)) and the pointPair encoder gap for decodeAcc_encode - owned by the accumulator perspective but gate contractRef_acc_complete's companion statements; needs the §9.5 sign-off the critic names.
- P-4a zeta_order: drop the field or change the test field (ZMod 17 has no element of order 3); recommended: drop zeta_order until a verifier-path consumer exists (the verifier never reads zeta).

## proof plan
### Bridge core: Dialect/Run/RunCommitted, Functional predicates, dialect_deterministic by op split, Run.det/RunCommitted.det, twoResponses counterexample, run-returns-abiTrue example, keccakOf_invariant by Step induction, Obs/ObsView/WorldEq/abiTrue defs, worldUnchanged_of_rollback [M4-Lean] est 3 days
prereqs: none (vendored dialect + Externals.lean already landed)
lemmas:
- Bridge.dialect_deterministic
- Bridge.Run.det
- Bridge.RunCommitted.det
- Bridge.twoResponses_nondet
- Bridge.keccakOf_invariant
- Bridge.RunCommitted_keccakOf
- Bridge.worldUnchanged_of_rollback
risks:
- `cases` on Step with the open dialect: Builtin unfolds to builtinWithExternal; use `change` to the match form before simp
- BitVec 256 literal arithmetic for accountKey distinctness (norm_num, not decide)
evidence: twoResponses gate shows hc is used; #print axioms on RunCommitted.det must be propext/Classical.choice/Quot.sound only; the abiTrue KAT and the hashOfBytes empty-input KAT are #eval gates
### Externals fold: toYulReq/ofOutcome/hits/honestOf/honestCalls/permissive, honestRelations_keys, honestCalls_functional, honest_le_permissive, Evaluator.calleeState/responseOf/rel/rel_functional [M4-Lean] est 1.5 days
prereqs: step 1
lemmas:
- Bridge.honestRelations_keys
- Bridge.honestCalls_functional
- Bridge.honest_le_permissive
- Bridge.Evaluator.rel_functional
risks:
- ByteArray ↔ List UInt8 round-trip lemmas (ByteArray.mk l.toArray).data.toList = l are not in core; prove via Array.toList_toArray
evidence: KAT on the G1ADD generator frame from relationKats_ok through honestOf (expect some true); perturbation: full-word target comparison fails the 2^160-aliased request
### ∀-runs contract layer: RunContractAll/StmtsContractAll, cons_halting, append, cond, switch (via selectSwitch), user-function call (lookupFun + callOk/callHalt inversion), halting loop countdown, block/restore lifting; constant-substitution (bindLocals) as a fuel pass with a 'substitution preserves Run' lemma [M4-Lean (blocking every per-partial spec)] est 4 days
prereqs: step 1
lemmas:
- StmtsContractAll.cons_halting
- StmtsContractAll.append
- StmtContractAll.cond
- StmtContractAll.switch
- StmtContractAll.call
- ExecLoopAll.countdown_or_halt
- substConsts_run
risks:
- Yul functions see only params ++ rets (callOk): constants inside AssemblyHelpers bodies must be substituted, never let-bound (survey constraint); R-37 fuel for the substitution pass
evidence: cons_halting instantiated on `revert(0,0); mstore(0,1)` with mid := False; the vendored StmtsContract.cons cannot state it
### Phase-4a algebra pulled in: MSMKZG.eval_addMsm/eval_scale/eval_fromBase under Wf, exists_smul_eq (cyclic prime-order groups), dualMsm_check_reorder, batched_complete, batched_atMostOneRoot, prepareMsgs_wf, modexpInv_correct, frOfRepr_frToRepr [pulled-forward finalPairing_spec / S5] est 4 days
prereqs: none
lemmas:
- MSMKZG.eval_addMsm
- MSMKZG.eval_scale
- exists_smul_eq
- dualMsm_check_reorder
- batched_complete
- batched_atMostOneRoot
- modexpInv_correct
- frOfRepr_frToRepr
risks:
- decideBool/P.decEqGₜ to Prop bridge lemma needed first (survey: none exists)
- msmSpecific drops zero scalars: additivity proof must handle the filterMap
evidence: ZMod 17 examples in the Spec/Lemmas style (scaled-by-zero and α = β counterexamples); modexp KAT on the inverse of 2
### Surface.lean + Precompiles/Codec hypothesis structures + ContractRefAcceptsAcc/LeanAccepts/DeploymentW/Run*/ObsEquiv/NoWriters/GenericX/NoLogupPanic defs; #check decodeAcc first; register files in Midfall.lean; build a fixture Surface from YulGolden ASTs for the non-vacuity gates [M5] est 3 days
prereqs: step 1; step 2
lemmas:
- extcodehash_of_deployment
- contractRefAcceptsAcc_noAcc
- instOfWords_of_decode (statement only; proof with P-12)
risks:
- decodeAcc's `-s` at Accumulator.lean:987 may not elaborate (no .olean); fallback is a local Fr-typed re-binding
- Generator.Api mutual block: validateForNumInstances needs equation lemmas for toExec reconciliation (D-P16 owed, other perspective)
evidence: DeploymentW instance on a toy world with a wrong codehash constant fails vkHash by #eval; contractRefAcceptsAcc_noAcc fails if frOfWord? reduces instead of rejecting
### Obligations.lean: LoweringCorrect structure with the eight fields; provable-now theorems lowering_equivalence (via ObsEquiv transport lemmas isReturn_of_view/returnData_of_view/worldUnchanged_of_view), lowering_equivalence_noAcc, contractRef_noAcc_of_semanticEquivalence; registered-hole theorems contractRef_acc_complete, verifyNative_iff_msgs_codec, xOf_eq; SORRY.md regeneration with an owner() arm; one digit band for the holes [M7/M8 statements] est 3 days
prereqs: step 5; step 4 for contractRef_acc_complete
lemmas:
- lowering_equivalence
- lowering_equivalence_noAcc
- contractRef_noAcc_of_semanticEquivalence
- Surface.shell_unfolds (hypothesis field)
- xOf_eq
risks:
- lean_grep.py apostrophe hazard in doc comments; checks.sh sort mismatch if hole lines span digit bands
evidence: Each field's refuting implementation listed in the declaration (trace render, swapped ec_pairing args, dropped trailing-bytes check, constant pairing oracle); checks.sh green with the new register rows
### finalPairing_spec proof (first calibration point): port AssemblyHelpers.yul ec_pairing + FinalPairing.yul to Block Op (P-13 first two partials), define Inv .pcs/.pairing over memory.pairingLhsMptr/pairingRhsMptr/accLhsMptr/accRhsMptr/finalPairingScratchMptr via loadWord/readBytes, prove the block contract with cons_halting + call + Eip2537.Holds.pairing_iff + dualMsm_check_reorder; accumulator arm via alphaOf preimage = the 0x1000 batch buffer bytes (keccak through hashOfBytes) and batchedCheck [pulled-forward (after M3)] est 6 days (first use of the whole architecture)
prereqs: steps 1-4; P-13 partials AssemblyHelpers/FinalPairing; Phase-4a algebra
lemmas:
- finalPairing_spec (field discharge for the fixture Surface)
- alphaOf_eq_contract_keccak
- pairingFrame_of_memory
risks:
- mcopy/readBytes/storeWord memory lemmas are not in the vendor; ~10 lemmas about copyWithin/loadWord disjointness needed
- MF-4: ERR_PRECOMPILE_FAILED vs ERR_PROOF_REJECTED both map to revert; the spec distinguishes neither
evidence: Swapping the ec_pairing call-site arguments in the ported block makes the proof fail at pairing_iff (R-11 is load-bearing); a constant-true product contradicts Holds via hNonDeg
### M7 composition: verifier_sound/complete/only_two_outcomes for the fixture Surface from the seven per-partial specs (vkLoading, transcriptParser, lagrange, quotientLin via QVM path, pcs, finalPairing, traceReturn) using StmtsContractAll.append over the Inv chain; NoLogupPanic enters at quotientLin, GenericX at lagrange; end_to_end_noAcc from verifyNative_iff_msgs_codec + repack_spec/calldata_roundtrip (P-12) + verifier_complete [M7] est unestimated (ROADMAP policy); lower bound 3 weeks
prereqs: all per-partial specs (other perspectives); P-11/P-12/P-13; verifyNative_iff_msgs_codec
lemmas:
- verifier_sound
- verifier_complete
- only_two_outcomes
- end_to_end_noAcc
risks:
- R-5/R-12 latent Exec panics (i32Abs, slice :370, inner_product, virtual selector) must each be shown unreachable under Supported or matched by a contract revert
- R-15 lazy zips in permutation/logup expressions must be reproduced or pinned by Supported sizes
- Evaluator frame contains the program: completeness needs the VK window of the frame pinned to vkRuntime
evidence: The side conditions are exercised by two KATs: the R-35 x3 mutation (both sides fail, NoLogupPanic holds) and a synthetic logup zero-denominator (contract value definite, Lean panics)
### M8: ShellModel object + irCheck (alpha-equivalence modulo constant substitution and solc renames, fuel-based) + generated yul% import of the via-ir IR after adding memoryguard/setimmutable to the vendored dialect; ir_refines by a simulation between the IR runtime and the shell at the view level [M8] est unestimated; dominated by the dispatcher model
prereqs: M7; D-P15 dialect additions; pinned solc IR text
lemmas:
- ir_refines
- shell_unfolds
- irCheck_sound
risks:
- Only one hex"…" literal and zero u256 annotations in the IR, but 76 user functions: the alpha-equivalence relation must be decidable and proved sound (stmtsBeq is too strict for renamed locals)
evidence: A planted rename in the generated quotes that changes semantics (swap two mstore addresses) must fail irCheck; memoryguard soundness holds for any value, completeness needs memoryguard ≤ 0x1000

## declarations
### Midfall.Yul.Bridge.Dialect / Run / RunCommitted  (def; statable-now; M4-Lean) — formal/Midfall/Yul/Bridge.lean
```lean
namespace Midfall.Yul.Bridge
open YulSemantics YulSemantics.EVM

/-- The open EVM dialect the generated verifier runs in: external calls answered by `calls`,
    no contract creation (PLAN's noCreates), `gas()` answered by `gas`. Nothing else is
    added over the vendored `evmWithExternal`; this is a name, not a second semantics. -/
@[reducible] def Dialect (calls : ExternalCalls) (gas : ExternalGas) : YulSemantics.Dialect :=
  evmWithExternal calls ExternalCreates.none gas

/-- Raw whole-program run at the open dialect (BigStep.Run, fuel-free). -/
def Run (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (st' : EvmState) (o : Outcome) : Prop :=
  YulSemantics.Run (Dialect calls gas) prog st0 V' st' o

/-- Observed run: the frame-boundary commit/rollback applied to the raw run. `committedState`
    is state-typed, so the vendored map is reused unchanged (P-BR item 2 answered). -/
def RunCommitted (calls : ExternalCalls) (gas : ExternalGas) (prog : Block Op) (st0 : EvmState)
    (V' : VEnv (Dialect calls gas)) (stObs : EvmState) (o : Outcome) : Prop :=
  ∃ st', Run calls gas prog st0 V' st' o ∧ stObs = committedState st0 st'
end Midfall.Yul.Bridge
```
hypotheses:
non-vacuity: example: Run (ExternalCalls.none) (ExternalGas.ofFun fun _ => 0) (yul% { mstore(0, 1) return(0, 32) }) EvmState.init [] st' .halt with st'.halted = some (.ret, abiTrue), built from Step.seqCons/builtinOk; a Dialect that made `mstore` stuck would make this example unprovable.

### Midfall.Yul.Bridge.ExternalCalls.Functional / ExternalGas.Functional / dialect_deterministic / Run.det / RunCommitted.det  (theorem-sorry; statable-now (det proof: 1 day; the op split is 70 trivial cases plus 7 external ones); M4-Lean) — formal/Midfall/Yul/Bridge.lean
```lean
/-- At most one response per request and pre-state (D-P10's determinism condition on `calls`). -/
def ExternalCalls.Functional (c : ExternalCalls) : Prop :=
  ∀ req st r₁ r₂, c.Call req st r₁ → c.Call req st r₂ → r₁ = r₂

/-- At most one remaining-gas word per state. `ExternalGas.ofFun f` satisfies it; `.any` does not. -/
def ExternalGas.Functional (g : ExternalGas) : Prop :=
  ∀ st g₁ g₂, g.Gas st g₁ → g.Gas st g₂ → g₁ = g₂

theorem ofFun_functional (f : EvmState → U256) : ExternalGas.Functional (ExternalGas.ofFun f) := by
  intro st g₁ g₂ h₁ h₂; simp [ExternalGas.ofFun] at h₁ h₂; rw [h₁, h₂]

/-- Every built-in of the open dialect is deterministic once both oracles are functional.
    Case split on `op`: call-family goes through `externalCall` (response unique by `hc`, then
    `finishCall` is a function); `create`/`create2` are either the static halt or have no
    derivation under `ExternalCreates.none`; `gas` by `hg`; every other op is `stepOp op args st =
    some r`, a function graph (the same argument as `EVM.evm_deterministic`). -/
theorem dialect_deterministic {c : ExternalCalls} {g : ExternalGas}
    (hc : c.Functional) (hg : g.Functional) (op : Op) : (Dialect c g).Deterministic op := by
  sorry

theorem Run.det {c g prog st0 V₁ st₁ o₁ V₂ st₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : Run c g prog st0 V₁ st₁ o₁) (h₂ : Run c g prog st0 V₂ st₂ o₂) :
    V₁ = V₂ ∧ st₁ = st₂ ∧ o₁ = o₂ :=
  YulSemantics.Run.det (dialect_deterministic hc hg) h₁ h₂

theorem RunCommitted.det {c g prog st0 V₁ s₁ o₁ V₂ s₂ o₂} (hc : c.Functional) (hg : g.Functional)
    (h₁ : RunCommitted c g prog st0 V₁ s₁ o₁) (h₂ : RunCommitted c g prog st0 V₂ s₂ o₂) :
    V₁ = V₂ ∧ s₁ = s₂ ∧ o₁ = o₂ := by
  obtain ⟨t₁, r₁, rfl⟩ := h₁; obtain ⟨t₂, r₂, rfl⟩ := h₂
  obtain ⟨rfl, rfl, rfl⟩ := Run.det hc hg r₁ r₂; exact ⟨rfl, rfl, rfl⟩
```
hypotheses:
- hc : c.Functional - necessary: externalCall is `∃ response, c.Call … ∧ result = .ok [flag] (finishCall …)`, so two responses give two results (twoResponses gate below)
- hg : g.Functional - necessary: `.gas` is `∃ g, gasOracle.Gas st g ∧ result = .ok [g] st`; under ExternalGas.any the op is not Deterministic (ecosystem Y-5, survey constraint on Run.det)
non-vacuity: theorem twoResponses_nondet : let c : ExternalCalls := ⟨fun req st r => req.target = 0x0f ∧ r.world = CallWorld.ofState st ∧ r.returndata = [] ∧ (r.success = true ∨ r.success = false)⟩; ∃ st₁ st₂ V₁ V₂, Run c (ExternalGas.ofFun fun _ => 0) (yul% { let s := staticcall(0, 0x0f, 0, 0, 0, 0) mstore(0, s) }) EvmState.init V₁ st₁ .normal ∧ Run c _ _ EvmState.init V₂ st₂ .normal ∧ st₁.memory 31 ≠ st₂.memory 31 - two hand-built derivations; shows hc is load-bearing (dualMsm_scale_check style).

### Midfall.Yul.Bridge.hashOfBytes / withKeccak / keccakOf_invariant  (theorem-sorry; statable-now (invariance proof ~0.5 day; ~45 Step constructors, each `simp [Res.state]` plus IH); M4-Lean) — formal/Midfall/Yul/Bridge.lean
```lean
/-- The List UInt8 ↔ ByteArray and U256 = H256 adapter: a Midfall hash as the vendored oracle. -/
def hashOfBytes (H : Midfall.Bytes → Midfall.H256) : List UInt8 → U256 :=
  fun l => H (ByteArray.mk l.toArray)

/-- Install `H` as the frame's keccak oracle (finding Y-2: the hash is `env.keccakOf`, not a
    dialect parameter, so hash-agnosticism is achieved at the state level). -/
def withKeccak (H : Midfall.Bytes → Midfall.H256) (st : EvmState) : EvmState :=
  { st with env := { st.env with keccakOf := hashOfBytes H } }

@[simp] theorem hashOfBytes_apply (H) (l : List UInt8) :
    hashOfBytes H l = H (ByteArray.mk l.toArray) := rfl

/-- The adapter round-trips: hashing the memory slice the EVM reads is hashing the ByteArray
    the Lean transcript builds from the same bytes. -/
theorem hashOfBytes_readBytes (H) (mem : Nat → UInt8) (p n : Nat) :
    hashOfBytes H (readBytes mem p n) = H (ByteArray.mk (readBytes mem p n).toArray) := rfl

/-- The state component a `Res` carries. -/
def Res.state {D : YulSemantics.Dialect} : Res D → D.State
  | .eres (.vals _ st) => st | .eres (.halt st) => st | .sres _ st _ => st

/-- No step of the open dialect changes `env.keccakOf`: `stepOp` touches other env fields
    (storageOf, transientOf, balanceOf, extCodeHashOf, selfBalance), `finishCall` goes through
    `CallWorld.install`, which also leaves it alone, and creates are absent. Rule induction on
    `Step`; no hypothesis on `calls` is needed because the world a response carries is installed
    only through `install`. -/
theorem keccakOf_invariant {c g funs V st code res}
    (h : Step (Dialect c g) funs V st code res) : (Res.state res).env.keccakOf = st.env.keccakOf := by
  sorry

theorem RunCommitted_keccakOf {c g prog st0 V' stObs o} (h : RunCommitted c g prog st0 V' stObs o) :
    stObs.env.keccakOf = st0.env.keccakOf := by sorry
```
hypotheses:
non-vacuity: If `CallWorld.install` were extended with keccakOf (or the dialect gained a hash-setting op) the induction's call case would fail; a KAT `#eval (hashOfBytes keccak256 (ByteArray.mk #[]).toList == keccak256 Bytes.empty) -- expect true` pins the adapter on the empty input against Keccak.lean's KAT vector.

### Midfall.Yul.Bridge.Obs / ObsView / isReturn / returnData / isRevertOrHalt / WorldEq / worldUnchanged / abiTrue  (def; statable-now; M4-Lean) — formal/Midfall/Yul/Bridge.lean
```lean
/-- What a caller observes: the committed state and the control-flow outcome (the vendored
    observation is this pair; there is no payload on `Outcome`, Ast.lean:353). -/
structure Obs where
  state : EvmState
  outcome : Outcome

/-- The caller-visible projection: halt kind + data, and the world components. Memory,
    activeWords and the variable environment are deliberately NOT part of it, so an IR whose
    memory layout differs from the shell model can still be ObsEquiv to it. -/
structure ObsView where
  outcome : Outcome
  halted : Option (HaltKind × List UInt8)
  storage : U256 → U256
  transient : U256 → U256
  logs : List LogEntry
  selfdestructs : List (U256 × Bool)
  balanceOf : U256 → U256
  extCodeOf : U256 → List UInt8
  nonceOf : U256 → U256
  storageOf : U256 → U256 → U256
  transientOf : U256 → U256 → U256

def Obs.view (o : Obs) : ObsView :=
  { outcome := o.outcome, halted := o.state.halted, storage := o.state.storage,
    transient := o.state.transient, logs := o.state.logs, selfdestructs := o.state.selfdestructs,
    balanceOf := o.state.env.balanceOf, extCodeOf := o.state.env.extCodeOf,
    nonceOf := o.state.env.nonceOf, storageOf := o.state.env.storageOf,
    transientOf := o.state.env.transientOf }

/-- `return(p, n)` fired (EVMExec.lean:840-843). -/
def Obs.isReturn (o : Obs) : Prop := ∃ d, o.state.halted = some (.ret, d)
def Obs.returnData (o : Obs) : List UInt8 :=
  match o.state.halted with | some (_, d) => d | none => []
/-- A non-committing halt: revert / invalid / invalidMemoryAccess / staticViolation.
    Running off the end (halted = none) and stop/selfdestruct are NOT included, so the
    only-two-outcomes conjunct really excludes them. -/
def Obs.isRevertOrHalt (o : Obs) : Prop := ∃ k d, o.state.halted = some (k, d) ∧ k.commits = false

/-- Equality of every world component (survey: memory/returndata/halted always differ). -/
def WorldEq (a b : EvmState) : Prop :=
  a.storage = b.storage ∧ a.transient = b.transient ∧ a.logs = b.logs ∧
  a.selfdestructs = b.selfdestructs ∧ a.env.selfBalance = b.env.selfBalance ∧
  a.env.balanceOf = b.env.balanceOf ∧ a.env.extCodeOf = b.env.extCodeOf ∧
  a.env.extCodeHashOf = b.env.extCodeHashOf ∧ a.env.nonceOf = b.env.nonceOf ∧
  a.env.storageOf = b.env.storageOf ∧ a.env.transientOf = b.env.transientOf
def Obs.worldUnchanged (st0 : EvmState) (o : Obs) : Prop := WorldEq st0 o.state

/-- The ABI encoding of `true`: the 32-byte big-endian word 1 (TraceReturn.yul:70-72 does
    `mstore(RETURN_MPTR, 1) return(RETURN_MPTR, 0x20)`). -/
def abiTrue : List UInt8 := (Midfall.natToBytesBE 1 32).data.toList
/-- The view of a successful run returning `abiTrue` with world `w`. -/
def returnView (w : EvmState) : ObsView := (Obs.view ⟨{ w with halted := some (.ret, abiTrue) }, .halt⟩)

theorem worldUnchanged_of_rollback {st0 st' : EvmState} {k d} (h : st'.halted = some (k, d))
    (hk : k.commits = false) : Obs.worldUnchanged st0 ⟨committedState st0 st', .halt⟩ := by
  simp [Obs.worldUnchanged, WorldEq, committedState_rollback h hk]
```
hypotheses:
non-vacuity: #eval (abiTrue.length == 32 && abiTrue.getLast? == some 1 && abiTrue.head? == some 0) -- expect true; an LE encoding would put 1 at the head. `isRevertOrHalt ⟨{init with halted := some (.stop, [])}, .halt⟩` is refutable by decide, so stop is not silently counted as revert.

### Midfall.Yul.Bridge.toYulReq / ofOutcome / failResp / hits / honestOf / honestCalls / permissiveCalls  (def; statable-now; M4-Lean) — formal/Midfall/Yul/Bridge.lean
```lean
def toYulKind : EVM.CallKind → Midfall.Yul.CallKind
  | .call => .call | .callcode => .callcode | .delegatecall => .delegatecall | .staticcall => .staticcall

/-- EVM request → Externals request (List UInt8 → ByteArray; Word256 = U256 definitionally). -/
def toYulReq (req : EVM.CallRequest) : Midfall.Yul.CallRequest :=
  { kind := toYulKind req.kind, gas := req.gas, target := req.target, value := req.value,
    input := ByteArray.mk req.input.toArray }

/-- A precompile changes no world state: the response world is the caller's own projection. -/
def ofOutcome (st : EvmState) (o : Midfall.Yul.CallOutcome) : CallResponse :=
  { success := o.success, returndata := o.returndata.data.toList, world := CallWorld.ofState st }
def failResp (st : EvmState) : CallResponse :=
  { success := false, returndata := [], world := CallWorld.ofState st }

/-- Target match on the 160-bit account key, the EVM's notion (EVMExec.lean:278); Externals'
    `accepts` compares the full word, which would let 2^160 + 0x0f miss the pairing precompile. -/
def hits (r : Midfall.Yul.ExternalCallRelation) (req : EVM.CallRequest) : Bool :=
  accountKey req.target == accountKey r.address

/-- The honest answer of the first relation whose address the request hits: `respond`, or a
    failed call when the input is invalid (EIP-2537: an error burns the gas and returns no data). -/
def honestOf (rels : List Midfall.Yul.ExternalCallRelation) (req : EVM.CallRequest) (st : EvmState) :
    Option CallResponse :=
  (rels.find? (fun r => hits r req)).map fun r =>
    match r.respond (toYulReq req) with
    | some o => ofOutcome st o
    | none => failResp st

/-- The disjunctive fold of finding Y-1: the four precompiles plus one evaluator slot. Functional
    iff the evaluator relation is and the five addresses are pairwise distinct on `accountKey`. -/
def honestCalls (product : Midfall.Yul.PairingProduct)
    (evalAddr : U256) (evalRel : EVM.CallRequest → EvmState → CallResponse → Prop) : ExternalCalls :=
  ⟨fun req st resp =>
    (honestOf (Midfall.Yul.honestRelations product) req st = some resp) ∨
    (accountKey req.target = accountKey evalAddr ∧ evalRel req st resp)⟩

/-- The soundness relation: any failure is permitted (gas is unmodelled, a precompile may be
    missing), a success must be the honest one, and no world change is ever reported. -/
def permissive (c : ExternalCalls) : ExternalCalls :=
  ⟨fun req st resp => resp.world = CallWorld.ofState st ∧ (resp.success = true → c.Call req st resp)⟩

theorem honest_le_permissive (c : ExternalCalls)
    (hw : ∀ req st r, c.Call req st r → r.world = CallWorld.ofState st) :
    ∀ req st r, c.Call req st r → (permissive c).Call req st r := fun _ _ _ h => ⟨hw _ _ _ h, fun _ => h⟩

/-- The four precompile keys are pairwise distinct and disjoint from the evaluator (Deployment). -/
theorem honestRelations_keys (product) :
    ((Midfall.Yul.honestRelations product).map (fun r => accountKey r.address)) = [0x0b, 0x0c, 0x0f, 0x05] := by
  sorry -- norm_num on four BitVec literals; relationKats_ok is only a #eval

theorem honestCalls_functional (product) (evalAddr) (evalRel)
    (hev : ∀ req st r₁ r₂, evalRel req st r₁ → evalRel req st r₂ → r₁ = r₂)
    (hdisj : accountKey evalAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat)) :
    ExternalCalls.Functional (honestCalls product evalAddr evalRel) := by sorry
```
hypotheses:
- hdisj - necessary: if evalAddr aliased 0x0f both disjuncts could fire with different responses (the Y-1 agreement obligation reduces to this)
- hev - necessary: Evaluator.rel is functional only because its inner run is deterministic (Evaluator.rel_functional below)
non-vacuity: Perturbation: redefine `hits` with `req.target == r.address` and the statement `honestOf rels {target := 2^160 + 0x0f, ...} st = some _` becomes false while the EVM would still dispatch to 0x0f; KAT: `#eval ((honestOf (honestRelations fun _ => true) req₀ EvmState.init).map (·.success)) -- expect some true` on the G1ADD generator frame from relationKats_ok.

### Midfall.Yul.Bridge.Evaluator.calleeState / Evaluator.responseOf / Evaluator.rel / Evaluator.rel_functional  (def; statable-now (the `_deployed` name is a Surface field, not hard-coded); M6/M7) — formal/Midfall/Yul/Bridge.lean
```lean
namespace Evaluator
/-- The frame the quotient evaluator's fallback runs in: zero memory, the caller's world view,
    `calldata := req.input` (the raw verifier frame, not ABI), `static := true` (the production
    call is a `staticcall`, QuotientAndLinearization.yul:35), the evaluator's own code/layout,
    and the caller's keccak oracle. -/
def calleeState (W : ExecEnv) (Lyt : Layout) (addr : U256) (st : EvmState) (req : EVM.CallRequest) : EvmState :=
  { EvmState.init with
    storage := st.env.storageOf addr, transient := st.env.transientOf addr,
    env := { Lyt.env with
      address := addr, caller := st.env.address, callvalue := 0, static := true,
      calldata := req.input, keccakOf := st.env.keccakOf,
      balanceOf := st.env.balanceOf, extCodeOf := st.env.extCodeOf, extCodeHashOf := st.env.extCodeHashOf,
      nonceOf := st.env.nonceOf, storageOf := st.env.storageOf, transientOf := st.env.transientOf,
      coinbase := W.coinbase, timestamp := W.timestamp, number := W.number, chainid := W.chainid } }

/-- The caller-visible response of a finished callee frame (Halo2QuotientEvaluator.sol:114 reverts
    empty on a bad frame length, :167 returns the compact output frame). -/
def responseOf (st : EvmState) (stObs : EvmState) : CallResponse :=
  match stObs.halted with
  | some (.ret, d) => { success := true, returndata := d, world := CallWorld.ofState st }
  | some (.stop, _) => { success := true, returndata := [], world := CallWorld.ofState st }
  | some (_, d) => { success := false, returndata := d, world := CallWorld.ofState st }
  | none => { success := true, returndata := [], world := CallWorld.ofState st }

/-- The evaluator slot of `honestCalls`: a request to the evaluator address is answered by RUNNING
    the evaluator's runtime block `rt` (the `_deployed` sub-object's code, via Object.subObject) in
    the closed dialect - the evaluator calls no precompile and never reads `gas()`
    (QuotientNumeratorBlock.yul has no staticcall/modexp). -/
def rel (W : ExecEnv) (Lyt : Layout) (addr : U256) (rt : Block Op) :
    EVM.CallRequest → EvmState → CallResponse → Prop :=
  fun req st resp => ∃ V' st' o,
    YulSemantics.Run EVM.evm rt (calleeState W Lyt addr st req) V' st' o ∧
    resp = responseOf st (committedState (calleeState W Lyt addr st req) st')

theorem rel_functional (W Lyt addr rt) :
    ∀ req st r₁ r₂, rel W Lyt addr rt req st r₁ → rel W Lyt addr rt req st r₂ → r₁ = r₂ := by
  intro req st r₁ r₂ ⟨_, _, _, h₁, rfl⟩ ⟨_, _, _, h₂, rfl⟩
  obtain ⟨_, rfl, _⟩ := EVM.run_det h₁ h₂; rfl
end Evaluator
```
hypotheses:
- None for functionality: EVM.run_det (closed dialect) is enough because the evaluator block is precompile-free; if a future evaluator calls a precompile, `rel` must move to Bridge.Run with honest precompiles and Run.det
non-vacuity: A deliberately wrong `responseOf` that mapped `.revert` to success would make the completeness proof's QuotientProgramInvalid check (`if iszero(staticcall(...)) { fail(...) }`) unreachable; gate: `responseOf st {init with halted := some (.revert, [])} |>.success == false` by decide.

### Midfall.Yul.Bridge.RunContractAll / StmtsContractAll + composition lemmas  (def; statable-now (each lemma ~0.5 day; inversion on Step with `cases h` works because the index is syntactic); M4-Lean (needed before any per-partial spec)) — formal/Midfall/Yul/Bridge.lean
```lean
/-- Partial correctness for EVERY run (the vendored RunContract is existential and says nothing
    about adversarial `calls`). -/
def RunContractAll (c : ExternalCalls) (g : ExternalGas) (prog : Block Op) (pre : EvmState → Prop)
    (post : EvmState → VEnv (Dialect c g) → EvmState → Outcome → Prop) : Prop :=
  ∀ st0 V' st' o, pre st0 → Run c g prog st0 V' st' o → post st0 V' st' o

def StmtsContractAll (c g) (funs : FunEnv (Dialect c g)) (stmts : Block Op)
    (pre : VEnv (Dialect c g) → EvmState → Prop)
    (post : VEnv (Dialect c g) → EvmState → VEnv (Dialect c g) → EvmState → Outcome → Prop) : Prop :=
  ∀ V st V' st' o, pre V st → ExecStmts (Dialect c g) funs V st stmts V' st' o → post V st V' st' o

/-- Sequencing with a head that may halt: the per-partial shape `reverted ∨ Inv k`. Inverts
    `Step.seqCons`/`Step.seqStop` (BigStep.lean:287-294). -/
theorem StmtsContractAll.cons_halting {c g funs stmt stmts pre mid post}
    (head : ∀ V st V' st' o, pre V st → ExecStmt (Dialect c g) funs V st stmt V' st' o →
        (o ≠ .normal ∧ post V st V' st' o) ∨ (o = .normal ∧ mid V' st'))
    (tail : ∀ V st, pre V st → StmtsContractAll c g funs stmts mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll c g funs (stmt :: stmts) pre post := by sorry

theorem StmtsContractAll.append {c g funs s₁ s₂ pre mid post}
    (h₁ : StmtsContractAll c g funs s₁ pre (fun V st V' st' o => (o ≠ .normal ∧ post V st V' st' o) ∨ (o = .normal ∧ mid V' st')))
    (h₂ : ∀ V st, pre V st → StmtsContractAll c g funs s₂ mid (fun _ _ V' st' o => post V st V' st' o)) :
    StmtsContractAll c g funs (s₁ ++ s₂) pre post := by sorry

/-- `if c { body }`: needs the expression to be deterministic-valued only through the post. -/
theorem StmtContractAll.cond {c g funs e body pre post}
    (hcond : ∀ V st cv st₁, pre V st → EvalExpr (Dialect c g) funs V st e (.vals [cv] st₁) →
        (cv = (Dialect c g).zero → post V st V st₁ .normal) ∧
        (cv ≠ (Dialect c g).zero → ∀ V' st' o, ExecStmt (Dialect c g) funs V st₁ (.block body) V' st' o → post V st V' st' o))
    (hhalt : ∀ V st st₁, pre V st → EvalExpr (Dialect c g) funs V st e (.halt st₁) → post V st V st₁ .halt) :
    ∀ V st V' st' o, pre V st → ExecStmt (Dialect c g) funs V st (.cond e body) V' st' o → post V st V' st' o := by sorry

/-- A loop that may halt in its body: countdown invariant plus a halting escape. -/
theorem ExecLoopAll.countdown_or_halt : True := trivial -- shape as ExecLoop.countdown with an extra `∨ (o = .halt ∧ Q st')` disjunct; stated in full in the file
```
hypotheses:
non-vacuity: Instantiate cons_halting on `yul% { revert(0,0) mstore(0,1) }` with mid := False: every run halts at the head, so the tail obligation is vacuous and the post must come from the head disjunct - the vendored `StmtsContract.cons` cannot even state this (its head must be .normal).

### Midfall.Lowering.Surface.Surface (the abstraction record)  (structure; statable-now; M5 (fields filled progressively)) — formal/Midfall/Lowering/Surface.lean
```lean
namespace Midfall.Lowering
open Midfall Midfall.Halo2 YulSemantics YulSemantics.EVM Midfall.Yul

/-- Everything PLAN 9.5 names that is not ported yet, as DATA over existing types. A theorem
    stated over `S : Surface` becomes a theorem about the deployment the day a `realSurface` is
    built (P-11/P-12/P-13); until then nothing here is proved vacuously, because every field is
    a function the statements consume, not a Prop assumed. -/
structure Surface (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
    [AdmissiblePairing G₁ G₂ Gₜ] where
  -- the verifier side (g in PLAN 9.5)
  E : VerifierEnv p G₁ G₂ Gₜ
  params : ParamsVerifierKZG G₁ G₂
  vk : VerifyingKey (Fr p) G₁
  cfg : Midfall.Generator.GeneratorConfig
  /-- The contract's positive-base table (artifacts.rs:181-245), NOT Exec `fixedBases` whose "-G"
      entry is the identity (defect). -/
  accFixedBases : Array (AccFixedBase G₁)
  /-- The VK_DIGEST word the contract hashes into alpha (Vk.lean:763 feToU256 ∘ frToRepr). -/
  vkDigest : Word256
  -- the lowered program (L)
  L : Lowered
  bindLocals : YulBlock           -- the constant-substituted locals block (R-37: produced with fuel)
  shell : YulObject               -- ShellModel: dispatcher wrapping headGuard ++ bindLocals ++ main
  shellLayout : EVM.Layout        -- code/dataoffset/datasize/immutable for the shell runtime
  evaluatorRuntime : Option (YulBlock × EVM.Layout)
  runtimeName : String → String   -- ir ↦ "<name>_<id>_deployed" (solc convention)
  -- codecs (P-12), typed per R-26.7: instances stay raw words
  repackProof : Bytes → Except Midfall.Generator.RepackError Bytes
  encodeCalldata : Bytes → Array (Fr p) → Except Midfall.Generator.GeneratorError Bytes
  decodeCalldata : Bytes → Option (List (Msg (Fr p) G₁) × Array Word256)
  -- render surface (P-13) and irCheck (M8)
  lower : Midfall.Generator.RenderOptions → Except Midfall.Generator.GeneratorError Lowered
  render : Midfall.Generator.RenderOptions → Except Midfall.Generator.GeneratorError String
  print : Lowered → String
  astOfMain : Midfall.Generator.RenderOptions → Option YulBlock   -- D-P15 generated yul% quote of the rendered main
  irCheck : YulObject → Bool
  -- predicates and the per-partial API (other perspectives fill them)
  Supported : Midfall.Generator.RenderOptions → Prop
  blk : Partial → YulBlock
  memory : Midfall.Generator.VerifierMemoryLayout
  Inv : Checkpoint → Snapshot p G₁ → EvmState → Prop
  snapshotOf : List (Msg (Fr p) G₁) → Array (Fr p) → Option (Snapshot p G₁)

inductive Partial | assemblyHelpers | accumulatorHelpers | vkLoading | transcriptParser | lagrange | quotientLin | pcs | finalPairing | traceReturn
inductive Checkpoint | start | vk | transcript | lagrange | quotient | pcs | pairing deriving DecidableEq

/-- The runtime block of a solc object (there is no `.runtime` field, Object.lean:80). -/
def Surface.irRuntime (S : Surface p G₁ G₂ Gₜ) (ir : YulObject) : Option YulBlock :=
  (ir.subObject (S.runtimeName ir.name)).map Object.codeBlock
end Midfall.Lowering
```
hypotheses:
non-vacuity: A `realSurface` must be constructible; until P-11..P-13 land, the only instance is a test Surface built from the poseidon fixture ASTs in YulGolden.lean (hand-transcribed), which already rejects a Surface whose `astOfMain` returns a block stmtsBeq-different from `L.main`.

### Midfall.Lowering.toExec / instOfWords? / ContractRefAcceptsAcc / LeanAccepts  (def; statable-now (decodeAcc must be #check'd first: Accumulator.lean has no .olean); M5) — formal/Midfall/Lowering/Surface.lean
```lean
/-- D-P16 bridge: the Generator encoding as the Exec stand-in decodeAcc is typed over. -/
def toExec (e : Midfall.Generator.AccumulatorEncoding) : Midfall.Halo2.AccumulatorEncoding :=
  { offset := e.offset, numLimbs := e.numLimbs, numLimbBits := e.numLimbBits,
    kind := match e.kind with
      | .pointAndScalar => Midfall.Halo2.AccumulatorEncodingKind.pointAndScalar
      | .pointPair => Midfall.Halo2.AccumulatorEncodingKind.pointPair }

/-- The contract's canonicality gate (TranscriptProofParser.yul:63-68): every instance word
    must be < r. Stated over raw words so the rejection is expressible (R-26.7). -/
def frOfWord? {p : ℕ} [Fact (Nat.Prime p)] (w : Word256) : Option (Fr p) :=
  if w.toNat < p then some (Nat.cast w.toNat) else none
def instOfWords? {p : ℕ} [Fact (Nat.Prime p)] (ws : Array Word256) : Option (Array (Fr p)) :=
  (ws.toList.mapM frOfWord?).map List.toArray

/-- PLAN 9.5 ContractRef.accepts with the accumulator arm, over the objects that exist:
    decodeAcc (4 args, Exec encoding via toExec, raw words), alphaOf (7 args, vk_digest word,
    kzgLhs/kzgRhs/accLhs/accRhs = d.left.eval, d.right.eval, fullyCollapse), batchedCheck (5 args,
    the contract's positive-base table). Hash-generic; keccak256 is the deployment. -/
def ContractRefAcceptsAcc {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
    [AdmissiblePairing G₁ G₂ Gₜ]
    (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params : ParamsVerifierKZG G₁ G₂) (vk : VerifyingKey (Fr p) G₁)
    (cfgAcc : Option Midfall.Generator.AccumulatorEncoding) (vkDigest : Word256)
    (fb : Array (AccFixedBase G₁)) (instW : Array Word256) (ms : List (Msg (Fr p) G₁)) : Bool :=
  match instOfWords? (p := p) instW with
  | none => false
  | some inst =>
    match prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms with
    | .error _ => false
    | .ok d =>
      match cfgAcc with
      | none => DualMSM.check d params
      | some enc =>
        match decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW with
        | none => false
        | some a =>
          let tbl := fb.map (fun b => (b.name, b.base))
          let (accL, accR) := a.fullyCollapse tbl
          batchedCheck params (alphaOf (p := p) H vkDigest E.g1 d.left.eval d.right.eval accL accR) d a tbl

/-- PLAN 9.5 LeanAccepts over raw calldata and raw instance words. -/
def LeanAccepts (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes) : Prop :=
  ∃ ms instW, S.decodeCalldata cd = some (ms, instW) ∧
    ContractRefAcceptsAcc S.E H S.params S.vk S.cfg.accumulator S.vkDigest S.accFixedBases instW ms = true
```
hypotheses:
- None as a def; the vkDigest link `S.vkDigest = frWord S.vk.transcriptRepr` and the fixed-base link to Vk.lean are Surface hypothesis fields (vkDigest_spec, accFixedBases_spec), kept out of Surface.lean's imports because Vk.lean pulls in Instances.ExponentModel
non-vacuity: theorem contractRefAcceptsAcc_noAcc : cfgAcc = none → (ContractRefAcceptsAcc … instW ms = true ↔ ∃ inst, instOfWords? instW = some inst ∧ ContractRefAccepts E H params vk inst ms = true) is provable by unfolding and is false if frOfWord? reduced mod p instead of rejecting (a word p+1 would then be accepted).

### Midfall.Lowering.DeploymentW (over ExecEnv, Y-2 hash coupling explicit)  (structure; statable-now; M5) — formal/Midfall/Lowering/Surface.lean
```lean
/-- What the world must look like, as hypotheses on an `ExecEnv` and on the hash `H` the frame
    runs with. `extcodehash` in the dialect is `projectedCodeHash` = `keccakOf (extCodeOf a)` for a
    non-empty account (EVMExec.lean:295-298, :822), so the codehash pin is a fact about H, not W:
    for the headline to hold for an arbitrary H, H must agree with the generation-time constant
    on the two code byte strings (otherwise VkLoading.yul:67-70 reverts VkMismatch while Lean
    accepts, and completeness fails). The vacuous `Lowering.Deployment` is superseded. -/
structure DeploymentW (W : ExecEnv) (H : Hash) (vkAddr quotientAddr : U256)
    (vkRuntime : Bytes) (expectedVkCodehash : Option Word256)
    (quotientRuntime : Option Bytes) (expectedQuotientCodehash : Option Word256) : Prop where
  keccak : W.keccakOf = Midfall.Yul.Bridge.hashOfBytes H
  wf : W.WF
  vkCode : expectedVkCodehash.isSome → W.extCodeOf vkAddr = vkRuntime.data.toList
  vkNonEmpty : vkRuntime.size ≠ 0
  vkHash : ∀ h, expectedVkCodehash = some h → H vkRuntime = h
  qCode : ∀ code, quotientRuntime = some code → W.extCodeOf quotientAddr = code.data.toList
  qHash : ∀ code h, quotientRuntime = some code → expectedQuotientCodehash = some h → H code = h
  qNonEmpty : ∀ code, quotientRuntime = some code → code.size ≠ 0
  disjoint : accountKey vkAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
             accountKey quotientAddr ∉ ([0x0b, 0x0c, 0x0f, 0x05] : List Nat) ∧
             accountKey vkAddr ≠ accountKey quotientAddr
  static : W.static = false   -- the production function is view; writes are excluded by NoWriters, not by the static bit

theorem extcodehash_of_deployment {W H vkAddr qa vkR eh qr eq} (D : DeploymentW W H vkAddr qa vkR eh qr eq)
    (h : eh = some hsh) : projectedCodeHash W W.balanceOf vkAddr = hsh := by
  sorry -- unfold projectedCodeHash; the length ≠ 0 branch; D.keccak, D.vkCode, D.vkHash, ByteArray.mk (toList.toArray) = id
```
hypotheses:
- vkNonEmpty - necessary: projectedCodeHash returns 0 for an EIP-161-empty account regardless of H
- vkHash as `H vkRuntime = h` rather than `keccak256 vkRuntime = h` - necessary for ∀H statements (finding Y-2; a constant pin would make every H ≠ keccak256 falsify completeness)
- disjoint - necessary for honestCalls_functional (Y-1 agreement)
- expectedVkCodehash = none is the embedded-VK render (VkLoading.yul:22-53), which reads no code: the fields are conditional so embedded renders need no W.extCodeOf fact
non-vacuity: Instantiate with W := { default with keccakOf := hashOfBytes keccak256, extCodeOf := fun a => if accountKey a = accountKey 0x1234 then rt else [] }: all fields discharge by rfl/decide except vkHash, which is `#eval keccak256 rt == h` - a wrong constant fails it, unlike the all-True placeholder.

### Midfall.Lowering.initState / callState / RunVerifier / RunContractIR / RunShell / ObsEquiv / NoWriters  (def; statable-now; M7/M8) — formal/Midfall/Lowering/Surface.lean
```lean
open Midfall.Yul.Bridge in
/-- The assembly's entry frame: arbitrary initial memory `mem₀` (verifier_sound is for ANY mem₀),
    calldata `cd`, the world `W`, hash `H`, the shell layout for immutables (`loadimmutable` reads
    `env.immutable`, EVMExec.lean:793). -/
def initState (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes) (mem₀ : Nat → UInt8) : EvmState :=
  { EvmState.init with memory := mem₀,
    env := { W with calldata := cd.data.toList, code := Lyt.code, dataOffset := Lyt.dataOffset,
             dataSize := Lyt.dataSize, immutable := Lyt.immutable, keccakOf := hashOfBytes H } }
/-- A fresh external call: zero memory (EVM-faithful; solc's `mstore(0x40, memoryguard(..))` is in the IR). -/
def callState (W) (Lyt) (H) (cd) : EvmState := initState W Lyt H cd (fun _ => 0)

def Surface.calls (S : Surface p G₁ G₂ Gₜ) (W : ExecEnv) (product : Midfall.Yul.PairingProduct) (quotientAddr : U256) : ExternalCalls :=
  honestCalls product quotientAddr (match S.evaluatorRuntime with
    | some (rt, Lyt) => Evaluator.rel W Lyt quotientAddr rt
    | none => fun _ _ _ => False)

/-- PLAN's RunVerifier: headGuard ++ bindLocals ++ main from an arbitrary memory, observed. -/
def RunVerifier (S) (W) (H) (cd) (mem₀) (c : ExternalCalls) (g : ExternalGas) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g (S.L.headGuard ++ S.bindLocals ++ S.L.main) (initState W S.shellLayout H cd mem₀) V' obs.state obs.outcome

/-- PLAN's RunContractIR over the imported via-ir object's runtime block (D-P15). -/
def RunContractIR (S) (W) (H) (ir : YulObject) (irLyt : EVM.Layout) (cd) (c g) (obs : Obs) : Prop :=
  ∃ rt V', S.irRuntime ir = some rt ∧ RunCommitted c g rt (callState W irLyt H cd) V' obs.state obs.outcome

/-- PLAN's RunShell: the hand-written dispatcher model wrapping the assembly. -/
def RunShell (S) (W) (H) (cd) (c g) (obs : Obs) : Prop :=
  ∃ V', RunCommitted c g S.shell.codeBlock (callState W S.shellLayout H cd) V' obs.state obs.outcome

/-- Observational equivalence at the view level (memory/VEnv are not observable). -/
def ObsEquiv (R₁ R₂ : Obs → Prop) : Prop :=
  ∀ v : ObsView, (∃ o, R₁ o ∧ o.view = v) ↔ (∃ o, R₂ o ∧ o.view = v)

/-- Fuel-bounded syntactic absence of world writers (sstore/tstore/log*/selfdestruct/create*/call/
    callcode/delegatecall). Fuel exhaustion answers `false` (conservative), per R-37. -/
def Op.isWriter : Op → Bool
  | .sstore | .tstore | .log0 | .log1 | .log2 | .log3 | .log4 | .selfdestruct
  | .create | .create2 | .call | .callcode | .delegatecall => true
  | _ => false
def noWritersFuel : Nat → YulBlock → Bool := sorry -- mutual with Expr/Stmt walkers; `0 => false`
def NoWriters (b : YulBlock) : Prop := ∃ n, noWritersFuel n b = true

/-- Only staticcalls and no writers ⇒ every run leaves the world alone (needs responses with
    `world = CallWorld.ofState st`, which `permissive` and the honest fold guarantee). -/
theorem Run_worldEq_of_noWriters {c g prog st0 V' st' o}
    (hw : ∀ req st r, c.Call req st r → r.world = CallWorld.ofState st)
    (hn : NoWriters prog) (h : Run c g prog st0 V' st' o) : WorldEq st0 st' := by sorry
```
hypotheses:
- NoWriters - necessary: trace renders emit log1 (TraceAndGasHelpers.yul:20-22) and call(gas(),…) (QuotientAndLinearization.yul:27); Supported.production is what makes the generated blocks NoWriters, and the IR shell adds none (solc view function). Alternative (open decision): assume `st0.env.static = true` instead - then the lemma is immediate from guardStatic, but it models a STATICCALL entry only
- hw - necessary: a `call` with value 0 installs the response world on success (finishCall), so a relation returning a modified world would break WorldEq even with no sstore
non-vacuity: Run_worldEq fails on `yul% { sstore(0,1) }` from a non-static state (storage 0 becomes 1): the NoWriters check on that block returns false, so the hypothesis is doing work.

### Midfall.Lowering.GenericX (xOf) / NoLogupPanic (side conditions of item C)  (def; statable-now (xOf_eq lemma owed: ~1 day); M7) — formal/Midfall/Lowering/Surface.lean
```lean
/-- The opening challenge `x`, replayed from the message stream: parseTrace, then the quotient-limb
    reads, then one squeeze (Verifier.lean:835-839). Three lines of schedule duplicated on purpose
    and pinned back to `verifyAlgebraicConstraints` by `xOf_eq` (owed), so R-30-style drift is a
    lemma failure, not a silent divergence. -/
def xOf (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Option (Fr p) :=
  let bytes := ms.foldl (init := Bytes.empty) (fun acc m => ByteArray.append acc (msgWire E m))
  let m : TranscriptM (Fr p) := do
    let _ ← parseTrace E.g1 Features.solidity vk #[#[1]] #[#[inst.toList]]
    let n := if Features.solidity.outerSingleHCommitment then 1 else vk.domain.getQuotientPolyDegree
    let _ ← tmReadN (hashableG1 E.g1) n
    tmSqueezeChallenge
  match m.run (Transcript.initWithHash H bytes) with | .ok (x, _) => some x | .error _ => none

/-- Completeness side condition (critic, Lagrange.yul:93-99 vs Domain.lean:251-258): the squeezed
    x is not an n-th root of unity. Lean/Rust accept such a proof, the contract reverts. -/
def GenericX (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms) (inst) : Prop :=
  ∀ x, xOf S.E H S.vk inst ms = some x → x ^ S.vk.n ≠ 1

/-- Soundness side condition (NEW, item C checked): the contract evaluates the logUp helper
    constraint by prefix/suffix products (yul_emit.rs:439-560, quotient.rs:1688-1880) and so
    computes a value at f_j(x)+β = 0, where Lean aborts (Logup.lean:279, logup.rs:460). Stated
    operationally - no snapshot needed - as "the Lean pipeline does not hit that panic". -/
def NoLogupPanic (S : Surface p G₁ G₂ Gₜ) (H : Hash) (ms) (inst) : Prop :=
  prepareMsgs (Gₜ := Gₜ) S.E H Features.solidity S.vk inst ms ≠
    .error (Fault.panic "proofs/src/plonk/logup.rs:460")
```
hypotheses:
- Both are necessary (not decorative): GenericX by the critic's counterexample x = ω^j outside the rotation window; NoLogupPanic by the k=1 arm `h*(f+β) - 1` which the contract evaluates to -1 while Lean faults
non-vacuity: On the NativeE2E fixture (Instances/, #eval only) GenericX holds and NoLogupPanic holds for the accepting proofs; mutating the committed-instance byte to 13 (R-35 KAT 14) is the x3 case, which both sides fail - a KAT that NoLogupPanic is NOT violated there distinguishes the two side conditions.

### Midfall.Lowering.LoweringCorrect (headline obligation fields)  (obligation-field; statable-now as fields; needs <P-11,P-12,P-13> for realSurface; M7 (sound/complete/two_outcomes/end_to_end), M8 (ir_refines), M3 (render_eq_print), pulled-forward (finalPairing_spec), M7 (traceReturn_spec)) — formal/Midfall/Lowering/Obligations.lean
```lean
open Midfall.Yul.Bridge in
/-- The headline obligations over a Surface. Every field quantifies over all H (hash-agnostic,
    PLAN 10.3) and over the production options; the deployment target is `H := keccak256`.
    Future deliverable: `theorem lowering_correct : LoweringCorrect realSurface`. -/
structure LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) (g2 : G2Enc G₂) : Prop where
  /-- ANY run of the assembly from ANY initial memory, under adversarial precompiles, that returns,
      returns `true` and Lean accepts. Side condition: the logUp denominators are non-zero (item C). -/
  verifier_sound : ∀ (o : RenderOptions) W H vkAddr qAddr cd mem₀ (gas : ExternalGas) obs,
    S.Supported o → DeploymentW W H vkAddr qAddr S.L.vkRuntime S.expectedVkCodehash S.quotientRuntime S.expectedQuotientCodehash →
    Eip2537.Holds product S.E.g1 g2 →
    RunVerifier S W H cd mem₀ (permissive (S.calls W product qAddr)) gas obs → obs.isReturn →
    (∀ ms instW inst, S.decodeCalldata cd = some (ms, instW) → instOfWords? instW = some inst → NoLogupPanic S H ms inst) →
    obs.returnData = abiTrue ∧ LeanAccepts S H cd
  /-- Lean accepts ⇒ a shell run exists under honest precompiles, and every honest run returns true.
      Side condition: x is not in the domain (critic, R-2 first face). -/
  verifier_complete : ∀ o W H vkAddr qAddr cd obs,
    S.Supported o → DeploymentW W H vkAddr qAddr _ _ _ _ → Eip2537.Holds product S.E.g1 g2 →
    LeanAccepts S H cd →
    (∀ ms instW inst, S.decodeCalldata cd = some (ms, instW) → instOfWords? instW = some inst → GenericX S H ms inst) →
    (∃ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
    (∀ obs, RunShell S W H cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
       obs.view = returnView (callState W S.shellLayout H cd))
  /-- Only two outcomes, read-only: return `true`, or a non-committing halt with the world unchanged. -/
  only_two_outcomes : ∀ o W H vkAddr qAddr cd gas obs,
    S.Supported o → DeploymentW W H vkAddr qAddr _ _ _ _ →
    RunShell S W H cd (permissive (S.calls W product qAddr)) gas obs →
    obs.view = returnView (callState W S.shellLayout H cd) ∨
    (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W S.shellLayout H cd))
  /-- M8: the imported via-ir object refines the shell model, observationally, for ANY calls/gas. -/
  ir_refines : ∀ ir irLyt, S.irCheck ir = true → ∀ W H cd c gas,
    ObsEquiv (RunContractIR S W H ir irLyt cd c gas) (RunShell S W H cd c gas)
  /-- D-P13 structural render_eq_print: the rendered text re-quoted (D-P15) is stmtsBeq-equal to
      the lowered main; the text equality of PLAN is false (R-39). -/
  render_eq_print : ∀ o L, S.lower o = .ok L →
    S.render o = .ok (S.print L) ∧ ∀ ast, S.astOfMain o = some ast → YulSemantics.SyntaxEq.stmtsBeq ast L.main = true
  /-- end_to_end_noAcc, with the RHS strengthened by an existence conjunct (PLAN's `∀ obs` alone is
      satisfied vacuously when no run exists, so its ← direction would be unprovable). -/
  end_to_end_noAcc : S.cfg.accumulator = none → ∀ o W vkAddr qAddr ir irLyt inst π,
    S.Supported o → DeploymentW W keccak256 vkAddr qAddr _ _ _ _ → Eip2537.Holds product S.E.g1 g2 →
    S.irCheck ir = true → S.E.g1.compressedRoundtrip →
    (∀ ms, decodeRust (Gₜ := Gₜ) S.E Features.solidity S.vk inst π = some ms → GenericX S keccak256 ms inst ∧ NoLogupPanic S keccak256 ms inst) →
    (verifyNative (Gₜ := Gₜ) S.E Features.solidity S.params S.vk inst π = .ok () ↔
      ∃ cd, (S.repackProof π >>= fun π' => (S.encodeCalldata π' inst).mapError id) = .ok cd ∧
        (∃ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
        ∀ obs, RunContractIR S W keccak256 ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
          obs.view = returnView (callState W irLyt keccak256 cd))
  /-- Pulled-forward finalPairing_spec: from Inv .pcs (PAIRING_LHS = d.left.eval, PAIRING_RHS =
      d.right.eval through toEip), the FinalPairing block either reverts or establishes Inv .pairing,
      and in production it reverts iff the batched/plain check is false (R-11: the swap is at
      FinalPairing.yul:88; the frame is [RHS|G2|LHS|NEG_S_G2] and Holds + pairing_reorder close it). -/
  finalPairing_spec : ∀ o W H qAddr snap gas,
    S.Supported o → Eip2537.Holds product S.E.g1 g2 →
    S.params.nG2Prepared = (AdmissiblePairing.g₂ : G₂)⁻¹ → g2.toEip (AdmissiblePairing.g₂) = S.g2BaseBytes → g2.toEip S.params.sG2⁻¹ = S.negSG2Bytes →
    StmtsContractAll (permissive (S.calls W product qAddr)) gas [S.hoisted] (S.blk .finalPairing)
      (fun _ st => S.Inv .pcs snap st)
      (fun _ _ _ st' o' => (o' = .halt ∧ ∃ d, st'.halted = some (.revert, d)) ∨ (o' = .normal ∧ S.Inv .pairing snap st'))
  traceReturn_spec : ∀ o W H qAddr snap gas, S.Supported o →
    StmtsContractAll (permissive (S.calls W product qAddr)) gas [S.hoisted] (S.blk .traceReturn)
      (fun V st => S.Inv .pairing snap st ∧ VEnv.get V "success" = some 1)
      (fun _ _ _ st' o' => o' = .halt ∧ st'.halted = some (.ret, abiTrue))
```
hypotheses:
- Eip2537.Holds - necessary in sound/complete/finalPairing: without it `product` is an arbitrary Bytes → Bool and the contract's accept set is unrelated to DualMSM.check
- compressedRoundtrip in end_to_end_noAcc - necessary (finding B1): a codec with toCompressed := fun _ => Bytes.empty makes verifyNative accept while the re-serialised prepareMsgs stream is short
- S.cfg.accumulator = none in end_to_end_noAcc - necessary (R-10): Rust verify_final batches with a POW2 sponge r, the contract with keccak α
- GenericX in complete/end_to_end - necessary (critic: x = ω^j makes Lean accept and Lagrange.yul:93-99 revert)
- NoLogupPanic in sound/end_to_end - necessary (item C, confirmed against yul_emit.rs and quotient.rs)
- nG2Prepared = g₂⁻¹ and the two G2 byte pins in finalPairing_spec - necessary (R-4: ParamsVerifierKZG.read uses the generator's g2 while the VK header embeds params.g2; the contract's G2_BASE/NEG_S_G2 are generation-time bytes)
- gas := ExternalGas.ofFun in completeness/end_to_end - necessary for the `∀ obs` conjunct to be about one run (determinism); soundness quantifies over every gas oracle
- returnView equality rather than `obs = .return abiTrue` - necessary because memory differs between IR and shell (ObsEquiv is view-level)
non-vacuity: Each field is refuted by a known wrong implementation: verifier_sound by a TraceReturn that returns `success` without `fail` (trace render: returns false ≠ abiTrue); verifier_complete by swapping the ec_pairing arguments back (R-11), which makes the honest run revert ProofRejected; only_two_outcomes by a trace render (log1 changes logs); end_to_end_noAcc by dropping the trailing-bytes check (cd ++ [0] would run while verifyNative's assertEmpty rejects); finalPairing_spec by a product oracle that is constantly true (then Inv .pairing would be established for a rejecting DualMSM, contradicting Holds).

### Midfall.Lowering.lowering_equivalence (3 conjuncts, derived)  (lemma-provable-now; provable-now (0.5 day once ObsEquiv transport lemmas exist); M8 (composition only; the content is in the fields)) — formal/Midfall/Lowering/Obligations.lean
```lean
/-- PLAN 9.5's headline, derived from the fields: soundness via ir_refines (view-level transport of
    isReturn/returnData/LeanAccepts), completeness via ir_refines on both conjuncts, and the
    two-outcome conjunct via ir_refines. The hypotheses are the union of the fields'. -/
theorem lowering_equivalence (hc : LoweringCorrect S product g2) (o : RenderOptions) (hsup : S.Supported o)
    (W : ExecEnv) (H : Hash) (vkAddr qAddr : U256) (hdep : DeploymentW W H vkAddr qAddr _ _ _ _)
    (hpc : Eip2537.Holds product S.E.g1 g2) (ir : YulObject) (irLyt : EVM.Layout) (hir : S.irCheck ir = true)
    (cd : Bytes)
    (hgen : ∀ ms instW inst, S.decodeCalldata cd = some (ms, instW) → instOfWords? instW = some inst →
              GenericX S H ms inst ∧ NoLogupPanic S H ms inst) :
    (∀ gas obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) gas obs → obs.isReturn →
        obs.returnData = abiTrue ∧ LeanAccepts S H cd) ∧
    (LeanAccepts S H cd →
        (∃ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs) ∧
        ∀ obs, RunContractIR S W H ir irLyt cd (S.calls W product qAddr) (ExternalGas.ofFun fun _ => 0) obs →
          obs.view = returnView (callState W irLyt H cd)) ∧
    (∀ gas obs, RunContractIR S W H ir irLyt cd (permissive (S.calls W product qAddr)) gas obs →
        obs.view = returnView (callState W irLyt H cd) ∨
        (obs.isRevertOrHalt ∧ obs.worldUnchanged (callState W irLyt H cd))) := by
  sorry -- provable now: transport each field through hc.ir_refines (isReturn/returnData/isRevertOrHalt/worldUnchanged are view-level; RunVerifier vs RunShell needs S.shell_unfolds, a Surface hypothesis that the shell's verifyProof arm runs headGuard ++ bindLocals ++ main from the dispatcher's memory)
```
hypotheses:
- hgen - inherits both side conditions because the three conjuncts split sound (NoLogupPanic) and complete (GenericX)
- S.shell_unfolds (Surface hypothesis field) - necessary to relate RunShell to RunVerifier: the dispatcher sets mem[0x40] and decodes ABI heads before the assembly; verifier_sound's ANY-mem₀ quantification is what makes this transport possible
non-vacuity: Not vacuous: the hypothesis set is satisfiable by the fixture Surface (see Surface non-vacuity) and the conclusion's first conjunct is falsifiable by a trace render.

### Midfall.Lowering.lowering_equivalence_noAcc  (lemma-provable-now; provable-now (hours; mirrors SemanticEquivalence.lean); M7) — formal/Midfall/Lowering/Obligations.lean
```lean
/-- Exact equivalence to the message-level verifier when no accumulator is configured (R-10 makes the
    hypothesis necessary). Provable today by unfolding LeanAccepts/ContractRefAcceptsAcc and the case
    analysis of `contractRefAccepts_iff_verifyMsgs`. -/
theorem lowering_equivalence_noAcc (S : Surface p G₁ G₂ Gₜ) (H : Hash) (cd : Bytes)
    (h : S.cfg.accumulator = none) :
    LeanAccepts S H cd ↔
      ∃ ms instW inst, S.decodeCalldata cd = some (ms, instW) ∧ instOfWords? (p := p) instW = some inst ∧
        verifyMsgs (Gₜ := Gₜ) S.E H Features.solidity S.params S.vk inst ms = .ok () := by
  sorry -- unfold; rw [h]; cases prepareMsgs …; simp [verifyMsgs, bind, Except.bind]
```
hypotheses:
- h : S.cfg.accumulator = none - necessary (R-10 counterexample X := Y^{-r})
non-vacuity: With `h` dropped the statement is false for any Surface with an accumulator and a proof whose KZG pairing holds but whose accumulator does not (decodeAcc some, batchedCheck false, verifyMsgs ok).

### Midfall.Lowering.contractRef_acc_complete / batched_complete / batched_atMostOneRoot  (theorem-sorry; statable-now; proofs ~2 days (bilinearity through Additive/LinearMap, Wf bookkeeping); M7 (contractRef_acc_complete), M9/S5 (batched_*)) — formal/Midfall/Lowering/Obligations.lean
```lean
/-- MSMKZG evaluation is additive and homogeneous on lockstep MSMs (msmSpecific zips with truncation;
    the `[1]` shortcut agrees with msmSpecific under Wf). Owed algebra (survey: no MSMKZG.eval lemma exists). -/
theorem MSMKZG.eval_addMsm {m₁ m₂ : MSMKZG (Fr p) G₁} (h₁ : m₁.Wf) (h₂ : m₂.Wf) :
    (m₁.addMsm m₂).eval = m₁.eval * m₂.eval := by sorry
theorem MSMKZG.eval_scale (m : MSMKZG (Fr p) G₁) (c : Fr p) : (m.scale c).eval = gsmul c m.eval := by sorry

/-- S5 completeness half: if both the KZG and the accumulator checks hold, the α-batched check holds
    for every α (bilinearity; no hypothesis on α). -/
theorem batched_complete (params : ParamsVerifierKZG G₁ G₂) (α : Fr p) (d : DualMSM (Fr p) G₁ G₂ Gₜ)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ) (tbl : Array (String × G₁)) (hL : d.left.Wf) (hR : d.right.Wf)
    (hd : DualMSM.check d params = true) (ha : KzgAcc.check a params tbl = true) :
    batchedCheck params α d a tbl = true := by sorry

/-- S5 soundness half: if the batched check holds for two distinct α and the KZG check fails, the
    accumulator check fails too - i.e. a bad pair has at most one root (PrimeOrderWith Gₜ p). -/
theorem batched_atMostOneRoot (params) (α β : Fr p) (hαβ : α ≠ β) (d a tbl) (hL hR)
    (h₁ : batchedCheck params α d a tbl = true) (h₂ : batchedCheck params β d a tbl = true) :
    DualMSM.check d params = true ∧ KzgAcc.check a params tbl = true := by sorry

/-- PLAN 9.5 contractRef_acc_complete, over the real arities: verifyMsgs accepts, the raw words decode
    to an accumulator whose own check holds (the contract is strictly stronger, R-26.4, so only this
    direction holds), hence ContractRefAcceptsAcc. -/
theorem contractRef_acc_complete (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash) (params) (vk) (enc : Midfall.Generator.AccumulatorEncoding)
    (vkDigest : Word256) (fb : Array (AccFixedBase G₁)) (instW : Array Word256) (inst : Array (Fr p)) (ms)
    (a : KzgAcc (Fr p) G₁ G₂ Gₜ)
    (hinst : instOfWords? (p := p) instW = some inst)
    (hv : verifyMsgs (Gₜ := Gₜ) E H Features.solidity params vk inst ms = .ok ())
    (ha : decodeAcc (p := p) (G₂ := G₂) (Gₜ := Gₜ) (toExec enc) E.g1 fb instW = some a)
    (hchk : KzgAcc.check a params (fb.map fun b => (b.name, b.base)) = true)
    (hWf : ∀ d, prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok d → d.left.Wf ∧ d.right.Wf) :
    ContractRefAcceptsAcc E H params vk (some enc) vkDigest fb instW ms = true := by
  sorry -- unfold; rw [hinst]; cases prepareMsgs with ok d; verifyMsgs ok gives check d; batched_complete
```
hypotheses:
- hWf - necessary: msmSpecific truncates on zip, so eval_addMsm is false for unequal lengths; a `prepareMsgs_wf` lemma (owed) discharges it for real outputs
- hchk over the CONTRACT table fb (positive bases, negated scalars), not Exec `fixedBases` whose "-G" is the identity - necessary, else the statement is about the wrong group element
- hαβ in atMostOneRoot - necessary: at a single α the batched equation can hold for a bad pair
non-vacuity: Spec.Lemmas.dualMsm_scale_check's ZMod 17 pattern: batched_complete fails if `scale` is replaced by the identity on only one channel (a wrong port of batchedCheck), and atMostOneRoot fails with α = β.

### Midfall.Lowering.dualMsm_check_reorder (pairing_reorder lifted)  (theorem-sorry; statable-now; ~1 day (needs decEqGₜ handling via decideBool_eq_true_iff); pulled-forward finalPairing_spec prerequisite) — formal/Midfall/Lowering/Obligations.lean
```lean
/-- The contract orientation e(right, G2) · e(left, -sG2) = 1 against DualMSM.check's
    e(left, sG2Prepared) · e(right, nG2Prepared) = 1, under the two params pins (R-4). Lifts
    Spec.Lemmas.pairing_reorder from the exponent ring: write left = xL • g₁, right = xR • g₁
    (every element of a prime-order cyclic group is a multiple of the generator - owed lemma
    `exists_smul_eq` from PrimeOrderWith), sG2 = s • g₂, and bilinearity turns both sides into
    rustEq/contractEq. -/
theorem dualMsm_check_reorder (d : DualMSM (Fr p) G₁ G₂ Gₜ) (params : ParamsVerifierKZG G₁ G₂)
    (hn : params.nG2Prepared = (AdmissiblePairing.g₂ (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ))⁻¹)
    (hs : params.sG2Prepared = params.sG2) :
    DualMSM.check d params = true ↔
      Additive.toMul (P.e (Additive.ofMul d.right.eval) (Additive.ofMul AdmissiblePairing.g₂) +
                      P.e (Additive.ofMul d.left.eval) (Additive.ofMul params.sG2⁻¹)) = (1 : Gₜ) := by
  sorry
```
hypotheses:
- hn - necessary (R-4): ParamsVerifierKZG.read sets nG2Prepared := g2Gen⁻¹ while ofParams uses g2⁻¹; the contract's G2_BASE is params.g2 asserted = P.g₂ (Vk.lean:806)
- hs - necessary: nothing in the structure ties sG2Prepared to sG2
non-vacuity: Spec/Lemmas.lean:131-138 examples already show rustEq/contractEq are neither trivially true nor false; the lifted statement fails if `hn` is replaced by nG2Prepared = g₂ (sign flipped).

### Midfall.Assumptions.Eip2537.Holds / G2Enc / modexpInv_correct  (structure; statable-now; modexpInv_correct provable-now (~1 day); M4-Lean (statements), finalPairing_spec (first use)) — formal/Midfall/Assumptions/Precompiles.lean
```lean
namespace Midfall.Assumptions
open Midfall Midfall.Yul

/-- The only G2 encoding the tree has is Generator.VkPointCodecs.g2Repr ∘ g2ToU256s (behind Vk.lean's
    Instances import), so the hypothesis layer takes an abstract 256-byte encoder. -/
structure G2Enc (G₂ : Type) where
  toEip : G₂ → Bytes

/-- What EIP-2537 must deliver for the generated verifier, relative to the codecs. `product` is
    Externals' PairingProduct oracle (the Fp12 hole). The frame is caller-ordered: FinalPairing.yul:88
    passes (PAIRING_RHS, PAIRING_LHS), so the pairs are [(rhs, G2), (lhs, NEG_S_G2)]. -/
structure Eip2537.Holds {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
    [Group G₁] [Group G₂] [Group Gₜ] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
    [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
    [P : AdmissiblePairing G₁ G₂ Gₜ]
    (product : PairingProduct) (c : G1Codec G₁) (c₂ : G2Enc G₂) : Prop where
  /-- The pairing check on encoded pairs is the Gₜ equation (additive form, 0 = identity). -/
  pairing_iff : ∀ ps : List (G₁ × G₂), ps ≠ [] →
    (product (pairingFrame (ps.map fun pr => (c.toEip pr.1, c₂.toEip pr.2))) = true ↔
      (ps.map fun pr => P.e (Additive.ofMul pr.1) (Additive.ofMul pr.2)).sum = 0)
  /-- Encodings are what the byte-level validators accept (on-curve, canonical, in the r-torsion). -/
  g1_valid : ∀ Q : G₁, ∃ pt, g1Of? (c.toEip Q) = some pt ∧ g1PointMsmValid pt = true
  g2_valid : ∀ R : G₂, ∃ pt, g2Of? (c₂.toEip R) = some pt ∧ g2PointValid pt = true
  /-- G1ADD on encoded points is the group law. -/
  g1add : ∀ Q R : G₁, g1AddOutput (g1AddFrame (c.toEip Q) (c.toEip R)) = some (c.toEip (Q * R))
  /-- G1MSM on encoded (point, scalar) pairs is msmSpecific. -/
  g1msm : ∀ pairs : List (G₁ × Fr p), pairs ≠ [] →
    g1MsmOutput (g1MsmFrame (pairs.map fun pr => (c.toEip pr.1, wordToBytesBE (Midfall.Halo2.frWord pr.2)))) =
      some (c.toEip (Midfall.Halo2.msmSpecific (pairs.map Prod.snd).toArray (pairs.map Prod.fst).toArray))
  /-- Every byte string the contract's validators accept decodes (needed when inputs come from calldata). -/
  eip_decode : ∀ b pt, g1Of? b = some pt → g1PointMsmValid pt = true → ∃ Q, c.ofEip? b = some Q ∧ c.toEip Q = b

/-- Modexp.Holds is NOT an assumption: modexpOutput is computed. The inversion frame returns x⁻¹. -/
theorem modexpInv_correct (x : ℕ) (hx : 0 < x) (hr : x < blsR) :
    modexpOutput (modexpInvFrame x) = some (bytesNatBE ((x : ZMod blsR)⁻¹).val wordBytes) := by
  sorry -- modPow correctness + ZMod.pow_card_sub_two_eq_inv with Fact (Nat.Prime blsR) from CompPoly (blsR = Assumptions.r by rfl)
end Midfall.Assumptions
```
hypotheses:
- Holds is a hypothesis structure because no in-tree pairing is computable (D-P1) and Externals' PairingProduct is an oracle; its satisfiability is NOT demonstrable in Lean today (the exponent model's toEip is not on the curve) - this is the trusted-base entry PLAN 1 names
- g1msm scalars are `frWord` words (canonical < r): necessary because G1MSM reduces scalars mod r implicitly, so a non-canonical word would alias
- eip_decode - necessary for soundness: calldata points reach G1MSM/pairing only after `common_uncompressed_g1` (canonical coordinates) and the subgroup check lives in the precompile (points_subgroup_checked)
non-vacuity: pairing_iff is falsified by a `product` ignoring order (constant) since `g1_valid` plus `hNonDeg` give a frame [(g₁,g₂)] with e ≠ 0 whose product must be false; modexpInv_correct is checked by `#eval (modexpOutput (modexpInvFrame 2)).map bytesToNatBE == some ((blsR + 1) / 2) -- expect true` (the known inverse of 2).

### Midfall.Assumptions.G1Codec.Laws / frOfRepr_frToRepr / verifyNative_iff_msgs_codec (restated, finding B1)  (theorem-sorry; statable-now; proof ~3 days (transcript-log invariant through parseTrace/multiPrepare); M7 prerequisite (end_to_end_noAcc)) — formal/Midfall/Assumptions/Codec.lean + Obligations.lean
```lean
structure G1Codec.Laws {G₁ : Type} (c : G1Codec G₁) : Prop where
  compressed : c.compressedRoundtrip
  eip : c.eipRoundtrip
  compressedWidth : ∀ Q, (c.toCompressed Q).size = g1CompressedWidth
  eipWidth : ∀ Q, (c.toEip Q).size = g1EipWidth

/-- Provable: the LE repr of a canonical scalar decodes to itself. -/
theorem frOfRepr_frToRepr {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≤ 2 ^ 256) (x : Fr p) :
    frOfRepr? (p := p) (frToRepr x) = some x := by sorry

/-- Finding B1: the frozen verifyNative_iff_msgs is false for a degenerate codec. The provable
    restatement adds the codec law (and uses Transcript.initWithHash keccak256 = initFromBytes, rfl). -/
theorem verifyNative_iff_msgs_codec (E : VerifierEnv p G₁ G₂ Gₜ) (F : Features) (params) (vk) (inst) (π : Bytes)
    (hc : E.g1.compressedRoundtrip) (hp : p ≤ 2 ^ 256) :
    verifyNative (Gₜ := Gₜ) E F params vk inst π = .ok () ↔
      ∃ ms, decodeRust (Gₜ := Gₜ) E F vk inst π = some ms ∧
        verifyMsgs (Gₜ := Gₜ) E keccak256 F params vk inst ms = .ok () := by sorry
```
hypotheses:
- hc - necessary: toCompressed := fun _ => Bytes.empty re-serialises a 48-byte-per-point stream to 32 bytes per scalar only, so prepareMsgs faults while verifyNative accepts (critic, survey)
- hp - necessary for frOfRepr_frToRepr (natToBytesLE truncates to 32 bytes)
non-vacuity: The degenerate codec is a concrete counterexample to the frozen statement (report, do not fix the frozen file); with hc the key lemma is `log_concat : (t.log.map (·.2)).foldl append = π.extract 0 t.pos`, an invariant of Transcript.read.

### Midfall.Lowering.contractRef_noAcc_of_semanticEquivalence (finding B3)  (lemma-provable-now; provable-now (SemanticEquivalence.lean must first be committed and built: it has no .olean); now) — formal/Midfall/Lowering/Obligations.lean
```lean
/-- The frozen `Statements.contractRef_noAcc` is provable now from the untracked
    `contractRefAccepts_iff_verifyMsgs` at H := keccak256; filling it needs a SHA re-pin, so the
    proof is recorded here under a new name. -/
theorem contractRef_noAcc_of_semanticEquivalence (E : VerifierEnv p G₁ G₂ Gₜ) (params) (vk) (inst) (ms) :
    (Lowering.ContractRefAccepts (p := p) (Gₜ := Gₜ) E keccak256 params vk inst ms = true) ↔
      verifyMsgs (Gₜ := Gₜ) E keccak256 Features.solidity params vk inst ms = .ok () :=
  contractRefAccepts_iff_verifyMsgs E keccak256 params vk inst ms
```
hypotheses:
non-vacuity: Same case analysis as SemanticEquivalence.lean:36-41; the Bool-to-Prop coercion in the frozen statement is `= true`, matched here explicitly.


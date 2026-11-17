<!-- Design memo behind PLAN-V3 (M2 — the object). Written by one design pass and kept as delivered, with local paths made repository-relative. Decision numbers inside predate PLAN-V3 §2 (D-P53 onward): follow that table. Where this memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. -->

# PLAN-V3 design memo - area OBJECT

Scope: what program the theorem is about, and what makes the render the generator's output for the verifier's own key. All numbers are `lake env lean` outputs at `6bde89f` (Lean sources identical to `f2fe99b`). Scratch files are under `docs/plans/V3-evidence/lean/object/`.

## 1. Coverage table at this commit (Cov1.lean)

Route: the computable proxies `poseidonPv` / `poseidonM` (PoseidonValid.lean:90-91). Both region partitions flatten exactly to the two token lists (two `true`).

| region of the main block | text tokens | AST tokens | agree | first difference |
|---|---|---|---|---|
| MF-2 guard (`vhMainAssemblyOpen` - 6) | 30 | 30 | yes | - |
| AssemblyHelpers | 1303 | 1303 | yes | - |
| AccumulatorHelpers | 823 | 0 | NO | region token 0 = global 1333 |
| TraceAndGasHelpers | 0 | 0 | yes (vacuous, trace = false) | - |
| verifierDirectSection | 0 | 0 | yes | - |
| `let r` / `let success` | 10 | 10 | yes | - |
| VkLoading | 223 | 223 | yes | - |
| TranscriptProofParser | 923 | 923 | yes | - |
| Lagrange | 501 | 501 | yes | - |
| Q&L / QuotientHelpers | 68 | 0 | NO | region token 0 = text index 3813 |
| Q&L / QuotientNumeratorBlock | 6384 | 0 | NO | region token 0 = text index 3881 |
| Q&L / linearization scope | 120 | 120 | yes | - |
| Pcs | 3623 | 3605 | NO | region token 0 (text opens a scope); the 3571 non-brace tokens are identical |
| FinalPairing | 22 | 22 | yes | - |
| TraceReturn | 23 | 23 | yes | - |
| closing brace | 1 | 1 | yes | - |
| TOTAL | 14054 | 6761 | `codegenAgrees = false` | global index 1333 |

ABI guard block: agrees, 52 tokens. Slice lengths in statements: `[1, 44, 3, 1, 225, 2, 3]`.

Function definitions. Text, 15: fail, scalar_inv, transcript_init, common_word, common_uncompressed_g1, squeeze_to, batch_invert, ec_pairing, load_acc_coord_shifted, is_bls_p_minus_one, check_acc_coord_packing, load_acc_coord, load_acc_point, q_program_fail, q_pow5. AST, 8: the first eight. Missing: five accumulator helpers (in AccumulatorHelpers) and q_program_fail, q_pow5 (inside the quotient partial, after `let success`).

## 2. Findings that change the plan

1. **The numerator block is mostly generated lines, not template** (Quot1.lean). Of 6384 tokens, 5431 (528 lines) are the model's line families: inline 895, native permutation 1038, native lookup 458, native identity 1044, post-VM 1996. The interpreter template plus program-field interpolations is 953 tokens. QUEUE G1.3 has it as 895 generated / 5489 template. The generated lines use seven line shapes only (`{`, `}`, `let`, `mstore(`, assignment, `for`, `if`).
2. **A total token-level parser handles all the generator text** (Parse1.lean, 120 lines, fuel-structural, `EVM.mkCall` for built-in versus user call). The whole main block parses to 74 statements and prints back to the same 14054 tokens. The three un-emitted regions parse (5 / 2 / 1 statements).
3. **The existing emitters are already the parse of their text, structurally** (`SyntaxEq.stmtsBeq`): AssemblyHelpers 8/8, VkLoading, TranscriptParser 44/44, Lagrange, linearization scope, FinalPairing, TraceReturn all `true`. Only pcs is `false` (1 statement against 225): the text is one wrapper scope holding eight block scopes and `emitPcsFromPlan` flattens them. `[Stmt.block (blocks.map Stmt.block)]` is `stmtsBeq`-equal to the parse.
4. **The complete main block exists constructively.** Today's emitters, pcs with scopes, and the three missing regions taken as parses of the model's own text give token agreement `true`, structural agreement `true`, 74 statements, slice lengths `[1, 44, 3, 4, 1, 2, 3]`, 15 functions, free names after inlining `["vk"]`, `noWritersFuel 20000 = true`.
5. **Scope (review fact 8) is confirmed and quantified.** The `.quotientLin` slice calls q_program_fail 13 times and q_pow5 6 times; `hoist R.helpers` has 8 functions, the program 15.
6. **The ported PCS emitter reproduces the artifact.** `poseidonM.pcsComputations == pcsDeployedComputations poseidonVerifierDump` is `true` (8 blocks, 19/10/45/25/10/89/122/25 lines). The PCS splice in `poseidonDerivedParts` is no longer needed.
7. **`LoweringPlan::new` is a glue port away** (Plan2.lean). Present in the tree: `metaDataForStableStaticLayout`, `Data.new`, `memoryRequirements`, `numPointSets`, `VerifierMemoryLayout.new`, `memoryLayoutFor`, `quotientIdentityParts`, `selectorFoldPlan`, `nativeGateIndices`, the VM builder with `shapeRecognizers`, `finish`, `quotientOperandModel`, `quotientVmGuards`, `validateGeneratorInvariants`, `certifyQuotientBuildsAgree`, `compactQuotientComputationBlocks`, `generateVk`. Absent: `quotient_program_plan`, `build_quotient_program_items(_with_limb_ops)`, `native_callback_scratch_words`, `quotient_stack_words_for_build`, `quotient_opcode_usage`, `quotient_mem_usage`, `quotient_template_program`, `validate_execution_manifest`, `compact_quotient_program_for`, and the constructor (about 480 Rust lines). My scratch port of all but `validate_execution_manifest`, run on `cs.json` and the payload, gives:
   - vk_mptr 0x2900, numPointSets 3, proofLen 4320, sortedSimple `[13, 14, 15, 17]`;
   - plan shape inline 4, items 9, native 3, permutation 7, lookup 3, tail 1, max power 21, tails `[21, 20, 17, 11]`;
   - VM build 88 bytes, 1 constant, max stack 2; constants and packed program words **equal the Rust VK payload words**;
   - every field of the typed-in `quotientDeployedProgram` reproduced;
   - `validateGeneratorInvariants` OK and dual-build certification OK;
   - the ported `compactQuotientComputationBlocks` equals the artifact-sliced blocks in post-VM (193), permutation (82), lookup (43), native identity (37/37/37); inline is 44+20+17+18 = 99 lines, which the artifact slicer had merged into one list;
   - **Halo2Verifier.sol rendered from the derived model equals the Rust artifact in all but one of 3024 lines (BUILD_ID), 175908 bytes, with nothing sliced from the artifact.**
8. **Three typed-in inputs are wrong.** `poseidonLayoutConfig.quotientStackWords := 24` (derived 25; the plan's `quotientStackHi` is 27744 against the derived 27776, which is what makes `guards.stackLast = 0x6c60`); `sortedSimple := [0,1,2,3]` (derived `[13,14,15,17]`); the PCS sizes (already recorded). `vkModelFromArtifact` (Contracts.lean:868-871) leaves `quotientConstOffsetWords`, `quotientConstWords`, `quotientProgramOffsetWords`, `quotientProgramWords` at `none/0`, so `plan.vk` is not the Rust `Halo2VerifyingKey`: the template-program step panics at quotient.rs:204 on it.
9. **Frozen clauses at the generator's plan:** circuitMeta `false`, layout `true`, invariants `true` (ObjectV3Full 7.4). This confirms B-1/F-1 by computation.
10. **The payload is derivable from the key data** (Key1.lean). The eleven header scalar words equal the values computed from `poseidonVkExec` (8 `true`). All 19 fixed and 8 permutation commitment words and the G1 base equal `G1Affine.toEip (G1Affine.ofCompressed? hex)` of `vk.json` / `params.json`. Not derivable today: the two G2 points (no computable G2 decompression found). Side observation: the payload's identity fixed commitments are at indices `[8, 10, 11, 12, 14, 16]` (six; review fact 3a lists five).

## 3. WP-G1 design

**Tie.** Keep the frozen token clause and add the structural one: the emitted AST equals the parse of the text. This closes the built-in/call blindness (B-4, F-10) and gives a statement-level reference to diff emitters against.

```lean
def parsedMain? (m : Model) : Option YulBlock := parseTokens (mainAssemblyTokens m)
def parsedGuard? (m : Model) : Option YulBlock := parseTokens (abiGuardTokens m)
def codegenStruct (main : YulBlock) (m : Model) : Bool :=
  (match parsedGuard? m with | some g => SyntaxEq.stmtsBeq (abiGuardBlock m) g | none => false) &&
  (match parsedMain? m with | some g => SyntaxEq.stmtsBeq main g | none => false)
```

**What is emitted, and from what.**
- AccumulatorHelpers (823 tokens, 5 functions; 1181 tokens with the accumulator on, adding `validate_public_accumulator`). The render does not read numInstances, k, vkMptr or proofLen (perturbation probe `true`). Interim: parse of `renderAccumulatorHelpers`. Structured emitter on demand.
- QuotientHelpers (68 tokens: q_program_fail 23, q_pow5 45; the limb7 arms are off). Interim: parse.
- QuotientNumeratorBlock: 953 template tokens plus the six line families. The families are permanently `parseLines` of the model's lists; they are the output of the ported `compactQuotientComputationBlocks`, and `GenAstQuotient.lean`'s AST twins cover only the per-identity evaluator layer, not the block producers.
- Pcs: restore the scopes.

**Does PlanView carry what the quotient region needs? No.** It has neither the `QuotientProgram`, the helper flags, nor the line families. The model has all of them. Proposed signatures (Program.lean is frozen, so this is one signed edit):

```lean
-- Lowering/GenAstDispatch.lean (refinable)
def GenAst.emitPartialM (pv : PlanView) (c : PartialCtx) : Partial → Block Op
  | .quotientLin => emitQuotientHelpers c ++ emitQuotientNumerator c ++ emitQuotientLin pv
  | .pcs => emitPcsScoped pv
  | q => emitPartial pv q
def GenAst.emitSlicesM (pv : PlanView) (c : PartialCtx) : Block Op :=
  Midfall.Lowering.partials.foldl (init := []) fun acc q => acc ++ emitPartialM pv c q

-- LoweringV2/Program.lean:98-99, :120-121, :125-126 (FROZEN)
def mainAsmRaw (pv : PlanView) (m : Model) : YulBlock :=
  let c := partialCtxOfVerifier m
  mainGuardBlock ++ GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers c ++ mainLocals ++
    GenAst.emitSlicesM pv c
def helpersOf (pv : PlanView) (m : Model) : YulBlock :=
  Inline.inlineContractConstants (constTableOf m)
    (GenAst.emitHelpers pv ++ GenAst.emitAccumulatorHelpers (partialCtxOfVerifier m))
def sliceOf (pv : PlanView) (m : Model) (q : Partial) : YulBlock :=
  Inline.inlineContractConstants (constTableOf m) (GenAst.emitPartialM pv (partialCtxOfVerifier m) q)
```

`asmOf`, `mainClosed` and `codegenAgrees` pass `m` through. `Render.prog`, `Render.slice`, `Render.helpers` keep their signatures. Existing block proofs need one bridge lemma per closed partial (`emitPartialM pv c .traceReturn = emitPartial pv .traceReturn := rfl`).

**Where the function definitions inside a partial go.** They stay in the `.quotientLin` slice, in text order, as `Stmt.funDef` (a no-op under `Step.funDef`). The scope becomes the hoist of the whole closed program:

```lean
-- LoweringV2/Statements.lean:109-110 (FROZEN)
def scope (c : ExternalCalls) (g : ExternalGas) : FunEnv (Bridge.Dialect c g) :=
  [hoist (Bridge.Dialect c g) (R.prog 0 0)]
```

`hoist` is a `filterMap` over top-level statements, so this is address-independent and conjunct 2 of `prog_slices_decomp` becomes a consequence of `hoist_prog_addr_indep`.

## 4. What ties the render to the generator

Options: (A) port the constructor and state `plan = new inputs`; (B) keep exported data and add decidable relations; (C) hybrid. **Recommendation: A for everything except the base VK payload, which stays an input tied by a key-coherence clause.** `generate_base_vk` needs the prover SRS and a pairing check; the commitments live in an abstract group. Everything else is a computation, and finding 7 shows it reproduces the fixture.

Typechecked in ObjectV3Full.lean (0 errors, 0 warnings, no sorry):

```lean
structure GenOut where
  plan : LoweringPlan Unit Unit
  qblocks : QuotientComputationBlocks
  model : Model

def generateAll (feat : Features) (delta : Fr p) (vk : VerifyingKey (Fr p) G₁)
    (cfg : GeneratorConfig) (payload : Halo2VerifyingKey) (inputs : ArtifactBuildInputs)
    (flags : RenderFlags) : Except Fault GenOut

def Render.generated : Except Fault GenOut :=
  generateAll Features.solidity R.E.delta R.vk R.cfg R.plan.vk R.inputs R.flags

def Render.GeneratedBy : Prop :=
  ∃ out, R.generated = .ok out ∧ out.plan = R.plan ∧ out.qblocks = R.qblocks ∧ out.model = R.model
```

`generateAll` = `ConstraintSystemMeta.new`, then `PlanNew.newFromVk` (stable static layout, proof layout, quotient plan and build, memory, template program, invariant validation, dual-build certification, `vkCarriesBuild`), then `compactBlocksOf`, `generateVerifierFromPlan`, `validateLayout`.

**Can the 13 clauses plus pins become one generated-by clause plus a few key-coherence clauses? Yes, seven clauses in four groups:**

```lean
structure Render.ValidV3 (R : Render p G₁ G₂ Gₜ) : Prop where
  generated : R.GeneratedBy
  inputs : R.inputs.numInstances = R.cfg.numInstances ∧ R.inputs.accEncoding = R.cfg.accumulator ∧
    R.inputs.k = R.vk.domain.k ∧ R.inputs.truncatedChallenges = Features.solidity.truncatedChallenges
  program : programOk R.pv R.model = true
  noWriters : NoWriters (R.prog 0 0)
  env : EnvAgrees R.E R.vk R.pv R.params R.sG2gen
  payload : PayloadAgrees R
  supported : SupportedV2 R
```

- `generated` replaces clauses 1-4, `validate_layout` (B-7), the VM-lowering gap (B+3) and makes `E.delta` reach the text (H-7).
- `program` is one Bool: `codegenStruct`, `constsCoherentWith`, `callsResolved`, `noShadow`, closedness including the guard block, and `0x80 ≤ transcriptMptr`. It replaces clauses 6, 7, 11, 12, 13 and the proposed pins D-P46 (table half) and D-P48. The landed version should also conjoin the frozen token clause; both were measured `true`.
- `payload` (`PayloadAgrees`, 13 fields: 11 header words, G1 base, G2 base, neg s G2, fixed and permutation commitments through `E.g1.toEip`) replaces `vkDigestWord` and v1's `VkSlotsAgree`. Its exact G2 wording belongs to the statements area; the object side needs it to exist.

Evaluation on the derived fixture render: `programOkWith mainV3 = true` (all five conjuncts `true`), `noWriters = true`, today's `mainAsmRaw` gives `false`.

Falsifiers: delta := 2 (the current `poseidonE.delta`) changes the text in 3 lines, so `GeneratedBy` is false at today's `poseidonRender`; one flipped `quotient_program` word is refused at vk.rs:457; a flipped omega word is NOT refused, which is why `PayloadAgrees` is needed in addition.

`Except.getOk` / `Except.eq_ok_getOk` typecheck (axioms: `propext`) and make `generated` provable by construction at a deployment. This closes DECISIONS-PENDING section 9 with no v1 edit.

## 5. Constants coherence: one clause

`expectedConsts (pv : PlanView) (m : Model) : List (String × Nat)` is the table as data, in `Constants.sol` order: addresses from `pv.memory`, lengths and codehash from `pv.vk`, calldata pointers from `pv.proofLayout`, the three optional arms and the gas numbers from the model, 14 template literals.

```lean
def constsCoherent (pv : PlanView) (m : Model) : Bool :=
  m.quotientDirect.isNone && constLinesLiteral m &&
  constTableOf m == expectedConsts pv m &&
  ((expectedConsts pv m).map Prod.fst).Nodup &&
  (progConstNames pv m).all fun x => ((expectedConsts pv m).map Prod.fst).contains x
```

At the fixture: `true`, 90 = 90 entries, all five conjuncts `true`; the program reads 78 of the 90. Falsifiers: transcript pointer moved in the plan view `false`; `proofEnd` moved `false`; model memory moved `false`. A model-only number (smoke gas) is rendered and expected from the same field, so it is not a falsifier; that is stated, not hidden.

Generic consequences, proved sorry-free for every `R` with `ValidV3` (axioms: the standard three):
`R.consts.lookup "VK_MPTR" = some (ptrAddr R.pv.memory.vkMptr)` and `R.consts.lookup "RETURN_MPTR" = some R.pv.memory.verifierReturnMptr`. The other lookups follow the same six-line script.

## 6. The artifact gate

Spliced or typed in today (PoseidonInputs.lean:283-292, DeployedProfile.lean:276-290):
- PCS lines from the artifact (`pcsDeployedComputations sol`);
- the five quotient line regions sliced from the artifact (`quotientDeployedCtx`, then `poseidonBlocks`);
- BUILD_ID copied from a transcribed context;
- typed in: `quotientDeployedProgram`, `poseidonLayoutConfig`, `poseidonVkMptr`, `poseidonProofLayout`, `sortedSimple`;
- the VK payload parsed back from the Rust `Halo2VerifyingKey.sol`.

What the port renders itself today: every line of `Halo2Verifier.sol` except BUILD_ID, given `cs.json` and the payload (finding 7); `Halo2VerifyingKey.sol` from the payload with its reservation fields (`true`).

Gate to require:

```lean
theorem artifact_gate_poseidon :
    (generateFromKeyData poseidonKeyData).map (fun o =>
      renderHalo2Verifier (rootCtxOfVerifier o.model) (partsOf o.model) == verifierSol &&
      renderHalo2VerifyingKey o.plan.vk == vkSol) = .ok true
```

with `poseidonKeyData` read only from `cs.json`, `vk.json`, `params.json` and a new `build.json`. Missing: (1) the glue port (scratch exists); (2) `generateVk` split into base and `generateVkFromBase`, plus a data-level base builder; (3) two G2 points in EIP-2537 form, by export or by an Fp2 square root; (4) the two BUILD_ID inputs (SRS fingerprint, feature string) exported; QUEUE R.5 already records that the committed BUILD_ID does not reproduce, so the dump must be re-exported with its inputs. Until (3) and (4) land, the honest gate is: all of `Halo2Verifier.sol` but the BUILD_ID line, payload as input.

## 7. The deployment target

Sepolia `moonlight-wrap` (README, deployment.json, sources): num_instances 0x13, k 0x14, has_accumulator 1 (acc_offset 11, 7 limbs), separate VK, embedded quotient VM (no `AUTHORIZED_QUOTIENT`), 27 fixed and 18 permutation commitments, solc 0.8.30 via-IR, no gas checkpoints. It violates `SupportedV2.noAcc` and needs X1; it needs neither X2 nor X3. More important: it was rendered by a superseded generator (`pragma ^0.8.24`, `TRANSCRIPT_MPTR = 0x80`, no BUILD_ID, no MF-2 guard, no q_program_fail), so the object of the theorem is not its source text and the `EntryFrame.fmp` assumption has no guard behind it there.

An untracked current-generator dump exists at `proofs/solidity-verifier/target/moonlight-wrap-solidity-dump` (accumulator on, embedded VM, separate VK). Tracked dumps inside the first-headline flags: hybrid-mt (k 13, 1 instance), rsa-signature (k 12, 22 instances), sha-preimage (k 13, 32 instances). ivc-keccak has an external evaluator and an accumulator.

Naming: call the target **fixture F1 = PoseidonExample, k = 6, 1 instance, test SRS**. Say in section 0 and in the English headline that no on-chain contract is covered. A claim about Moonlight needs X1 and a redeployment or a regenerated artifact under the current templates.

## 8. Frozen edits, in one re-pin (D-P51)

Program.lean: :98-99 `mainAsmRaw` (model argument, accumulator helpers), :114-116 `asmOf`, :120-121 `helpersOf`, :125-126 `sliceOf`, :132-134 `mainClosed` (guard block), :190-194 codegen (add `codegenStruct`), :51-60 and :92-97 docstrings.
Statements.lean: :109-110 `scope`; :136-168 delete `vkPins` / `vkProgressPins`; :182-217 `Valid` becomes `ValidV3`; :66-70, :179-185, :203-205 docstrings.
Refinable: Inv.lean unchanged; GenAstDispatch.lean:131-135 and :188-196; new `Lowering/YulParse.lean`, `LoweringV2/Consts.lean`, `LoweringV2/Generated.lean`, `Generator/PlanNew.lean`; Blocks.lean:206-225 and :276-285.

## 9. Milestones

- M-OBJ-1 the program is complete: `programOk = true` at the fixture (OBJ-1, 2, 3, 4, 5).
- M-OBJ-2 the render is generated: `generateAll` reproduces the artifact but for BUILD_ID (OBJ-6, 7).
- M-OBJ-3 `ValidV3` stated, decidable half proved at the fixture (OBJ-8, 9).
- M-OBJ-4 the artifact gate with nothing from the artifact (OBJ-10, 11, 12).
- M-OBJ-5 optional: structured emitters and more fixtures (OBJ-13 to 16).

## 10. Pitfalls met while measuring

- `data` and `show` are not usable as binder names in files importing the generator; `![..]` is matrix notation, write `!([..].contains t)`; `Op` is ambiguous between `EVM.Op` and `Lowering.Op` inside `Midfall.LoweringV2`.
- A mutation falsifier that hits a comment is invisible (the first `0x3cc81b89` in QuotientHelpers is in a comment); target a code token.
- `LoweringPlan` and `Model` have no `BEq`: compare by render or by field.
- `metaDataForStableStaticLayout` reads only `meta_` and `numInstances` of `VerifierBuildInputs`; the scratch passes a dummy `ParamsKZG` over `Unit`. Refactor the three Vk.lean functions to take those two values.
- The glue port was exercised on one circuit; only 10 of 31 opcode arms and no limb shapes occur there.

Please review these results for accuracy and completeness before relying on them.

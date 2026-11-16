# Review: `formal/` — Lean verifier ⇔ generated Solidity/Yul

Scope: `formal/` at `979f358` (2026-11-16). Focus: the lowering (semantic-equivalence) track, its
headline theorem and proof strategy, the agent's work log, and the solc-IR question.
Companion proof: [ReviewRefutation.lean](./ReviewRefutation.lean) (kernel-checked, see §2).

---

## 0. Summary

1. **The headline `lowering_equivalence` is vacuous.** Its hypothesis `hc : LoweringCorrect S product`
   is *unsatisfiable for every Surface `S` and every `product`*. I proved this in Lean
   (`ReviewScratch.not_LoweringCorrect`, axioms: `propext`, `Classical.choice`, `Quot.sound` only).
   The theorem the work log announces as "THE HEADLINE THEOREM OF THE PROJECT IS PROVED" (commit
   `0eba62c`) is therefore an implication from `False`.
2. **The cause is the solc-IR track you suspected.** `LoweringCorrect.ir_refines` quantifies over
   *every* object passing `Surface.irCheck`, a check the tree itself proves accepts arbitrary programs.
   That obligation exists because Fable's plan (amendment of 2026-10-23) made "solc IR translation
   validation" a **required** step (PLAN §1, §7, §9.5, M8), and D-P38 adopted it. Your 2026-11-15
   correction ("the deliverable is the generator's Yul", `d0dd244`) was implemented by moving the solc
   bridge *into the hypothesis bundle* rather than deleting it.
3. **Even after removing solc, the statements are not about the Lean codegen.** The lowered program
   `S.L`, the render function `S.lower`, the plan `S.plan`, `S.blk`, `S.shell`, … are **free fields** of
   a record. Nothing computes them from the VK/config with the ported generator; the PlanView is not
   derived from the VK, and at the only deployment fixture the two describe different circuits
   (`readScheduleAgrees_refuted_at_deployment`).
4. **The M7 strategy (per-partial Hoare contracts) is stated over the wrong program.** The contracts
   talk about *un-inlined* fragments whose helper calls are stuck (6 of 8 helpers read contract
   constants they cannot see), while the run relations execute the *inlined* program. The ∀-runs
   contracts are vacuous exactly on the interesting paths (e.g. `finalPairing` through `ec_pairing`),
   and the "progress" (completeness) contracts never assert that a run exists.
5. **Real progress so far** on the actual equivalence: 1 of 10 per-partial spec theorems
   (`traceReturn_spec`, the 3-statement return block). No term of `LoweringCorrect` or `PartialSpecs`
   exists anywhere. The "40 sorries" register does not count any `LoweringCorrect`/`PartialSpecs`
   field, so it understates the remaining work by most of the project.
6. **Solid, reusable work exists**: the Exec port and conformance replay, `verifyNative_iff_msgs`
   (byte-level ⇔ message-level verifier, genuinely proved), the `GenAst` AST emitter for all seven
   partials, the yul-semantics bridge, the inlining transform with its shadowing lemmas, the QVM
   per-arm agreement lemmas, and `traceReturn_spec`'s step-inversion machinery.

---

## 1. What the main lowering theorem says and how it is meant to be proved

### 1.1 Objects

| object | file | meaning |
|---|---|---|
| `Surface p G₁ G₂ Gₜ` | `Lowering/Surface.lean:200` | a record bundling the verifier side (`E`, `params`, `vk`, `cfg`) **and** the lowered program side (`L`, `lower`, `plan`, `blk`, `shell`, `bindLocals`, `evaluatorRuntime`, `runtimeName`, …) plus ~12 "pin" equations between them |
| `RunVerifier S W H cd mem₀ c g obs` | `Surface.lean:839` | committed run of `armProgram S` = `inlineContractConstants consts (L.headGuard ++ bindLocals ++ L.main)` from an arbitrary memory |
| `RunShell` | `Surface.lean:862` | committed run of `S.shell.codeBlock` (pinned equal to `armProgram S`) from zeroed memory |
| `RunContractIR S … ir irLyt …` | `Surface.lean:850` | committed run of the runtime sub-object of a **solc IR object** `ir` |
| `ShellModel.wrap` | `Yul/ShellModel.lean:316` | a hand-written Yul model of **solc's dispatcher** (prologue, selector switch, callvalue, ABI bounds, immutables) around `armBody S` (the **un-inlined** concatenation) |
| `LeanAccepts S H cd` | `Surface.lean:883` | `decodeCalldata` succeeds and `ContractRefAcceptsAcc` (the Lean verifier, with the contract's α-batching in accumulator mode) accepts |
| `ObsEquiv R₁ R₂` | `Surface.lean:871` | the two run predicates reach exactly the same set of observable views (halt payload + world) |

### 1.2 The headline (`Lowering/Obligations.lean:665`)

```
lowering_equivalence S product (hc : LoweringCorrect S product) hsup W H vkAddr qAddr hdep hpc henv
    hcodec hwl cd hsel hside g₀ :
  (∀ obs, wrap … (permissive calls) gas obs → obs.isReturn → returnData = abiTrue ∧ LeanAccepts)   -- soundness
∧ (LeanAccepts → (∃ obs, wrap … honest …) ∧ ∀ obs, wrap … honest … → obs.view = returnView …)   -- completeness
∧ (∀ obs, wrap … → returnView ∨ (revertOrHalt ∧ worldUnchanged))                                 -- two outcomes
```

### 1.3 Proof architecture as designed

1. **Snapshot.** Run the Lean verifier on the decoded messages and record every intermediate value
   (challenges, evaluations, Lagrange values, quotient, PCS MSM, pairing inputs): `snapshotOf`.
2. **Invariant `Inv k`.** At each of seven checkpoints between partials, relate EVM memory (addresses
   from the memory layout) and the `success` local to the snapshot (`Lowering/Inv.lean:824`).
3. **Per-partial contracts** (`Lowering/Partials.lean:294`, `PartialSpecs`): for each of VkLoading,
   TranscriptParser, Lagrange, QuotientAndLinearization, Pcs, FinalPairing, TraceReturn —
   *sound*: every run from `Inv pre` reverts or ends in `Inv post`; *progress*: under honest
   precompiles every run ends normally in `Inv post`; *rejects*: if Lean has faulted, every run reverts.
4. **Compose** the seven slices into `verifier_sound` / `verifier_complete` for the whole assembly (M7).
5. **Transport** from the assembly to the entry path (M8): `ir_refines` relates a solc IR object to
   `RunShell`; instantiated at `ShellModel.modelIr S` (whose runtime *is* `wrap`) it yields the headline.

In the current tree, steps 4 and 5 are **not proofs but hypotheses**: `verifier_sound`,
`verifier_complete`, `only_two_outcomes`, `ir_refines`, `render_eq_print`, `end_to_end_noAcc`,
`partials`, `qvm_validated_noBoundsFault`, `accFixedBases_producer`, `readScheduleAgrees` are the ten
fields of `LoweringCorrect`. The proof of `lowering_equivalence` (≈60 lines) only threads them together.

---

## 2. Finding F1 (critical): `LoweringCorrect` is uninhabited

**Statement proved** ([ReviewRefutation.lean](./ReviewRefutation.lean)):

```lean
theorem not_LoweringCorrect (S : Surface p G₁ G₂ Gₜ) (product : PairingProduct) :
    ¬ LoweringCorrect S product
-- 'ReviewScratch.not_LoweringCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Mechanism.** The field

```lean
ir_refines : ∀ (ir : YulObject) (irLyt : EVM.Layout), S.irCheck ir = true →
  ∀ W H cd c g₀, c.WorldLocal →
    ObsEquiv (RunContractIR S W H ir irLyt cd c (ofFun _ => g₀)) (RunShell S W H cd c (ofFun _ => g₀))
```

quantifies over every `ir` passing `Surface.irCheck`, which only checks that the runtime sub-object
exists and has no unresolved *top-level* user call (`Surface.lean:821`). Two such objects:

* runtime `[]` — runs off the end (one committed run, outcome `.normal`);
* runtime `[let y := zz]` — reads an unbound variable, so it has **no** derivation.

Both pass `irCheck`. `ObsEquiv` with the same `RunShell` for both forces them `ObsEquiv` to each other,
so the stuck program would need a run with the empty program's view — contradiction. No determinism
lemma is needed (contrary to the P-INLINE commit, which believed refuting `ir_refines` needs the open
hole `dialect_deterministic`).

The tree already contained both halves: `IrCheckBlindness.irCheck_accepts_both_outcomes` (a `return`
object and a `revert` object both pass) and `irCheck_admits_different_observables`. The consequence for
the bundle was never drawn because the non-vacuity rule (D-P23) was applied to the *side* hypotheses
(`SupportedS`, `DeploymentW`, `EnvAgrees`, `Holds`, …) and never to `hc` itself.

**Related, same mechanism.** `end_to_end_noAcc` also quantifies over every `ir` with
`S.irCheck ir = true`; instantiated at the stuck object its right-hand side is false, so the field
asserts that no proof ever verifies natively under its hypotheses.

**How to verify yourself** (does not touch the repo's `.lake`): compile
`Midfall/Lowering/Obligations.lean` to a scratch olean directory and run
`lean -DautoImplicit=false ReviewRefutation.lean` with that directory first on `LEAN_PATH`
(this is what I did; peak RSS ≈ 2.1 GiB). Or drop the file into `Midfall/Instances/` and `lake build`.

**Fix.** Delete `ir_refines` (and `RunContractIR`, `irCheck`, `runtimeName`, `irRuntime`) from the
obligations — see §4 for the replacement boundary. Add a standing rule: *a theorem whose hypothesis is a
structure of obligations must ship with a proof that the structure is consistent (ideally an instance
at the deployment), not only with witnesses for its side hypotheses*; and never put a field that
universally quantifies over programs/objects into such a bundle.

---

## 3. The other weak statements, with fixes

### F2 (critical) — the theorem is not about the Lean codegen

`Surface.L : Lowered`, `Surface.lower : RenderOptions → Except _ Lowered` (with `lower_ok : lower o₀ = .ok L`),
`astOfMain`, `blk`, `plan : PlanView`, `shell`, `bindLocals`, `evaluatorRuntime`, `runtimeName` are all
**free fields**. `render_eq_print` relates two free fields to each other. `BlkIsEmitter` (a hypothesis
of the per-partial specs, `Partials.lean:268`) does tie `blk`/`L.main` to `GenAst.emitPartial`/
`emitMain` — but at the free `S.plan`, and `L.headGuard`, `bindLocals`, `shell` remain free.

Consequences already measured by the agent: ~20 rounds of "a copied fact had no pin" repairs (R-58,
R-60, P-RESTORE2/3, P-GATEINTEG: "28 obligation fields had no pin"), and gates written to police them.
This whole defect class disappears if the record is *computed*.

**Fix.** Replace the record by a function of the generator inputs:

```lean
def planViewOf (vk : Halo2VerifyingKey) (cfg : GeneratorConfig) (o : RenderOptions) :
    Except GeneratorError PlanView                  -- port of LoweringPlan::new (P-11)
def asmOf (pv : PlanView) : YulBlock :=             -- the closed body of verifyProof's main assembly
  inlineContractConstants (contractConstantsOf pv) (emitHeadGuard pv ++ emitMain pv)
```

and state everything over `hpv : planViewOf vkPayload cfg o = .ok pv` and `asmOf pv`. The pins become
`rfl`/definitional lemmas, and the link to the Rust generator stays where D-P13 put it (golden AST /
token equality of `print (asmOf pv)` against the Lean text port and the Rust output).

### F3 (high) — PlanView is not derived from the VK

`S.vk` and `S.plan` are independent. At `realSurface` the plan is the 72-slot poseidon layout while the
VK is a one-advice-column toy (8 reads), with every pin, `SupportedS`, `DeploymentW` and `EnvAgrees`
green; `readScheduleAgrees_refuted_at_deployment` proves the field false there. Any "proof" of
`LoweringCorrect` at such a Surface would say nothing about a real deployment. **Fix:** F2 (`planViewOf`).

### F4 (high) — per-partial contracts are over un-inlined fragments

`PartialSound`/`PartialProgress` are about `S.blk q S.plan` (= `GenAst.emitPartial`, un-inlined) in
`mainScope S` (= `hoist S.L.main`, un-inlined). After P-INLINE the run relations execute the *inlined*
program, but `Partials.lean` never mentions `inlineContractConstants`, and there is no lemma relating
runs of the two. Because a Yul function is not a closure (`Step.callOk` binds only params and rets),
the 6 of 8 helpers that read contract constants (`helperOwnFree_count_ok`) are stuck in every
un-inlined run. Example: the no-accumulator `finalPairing` slice is
`[if iszero(success) { fail(ERR_PRECOMPILE_FAILED) }, success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)]`,
and `ec_pairing`'s body reads `G2_BASE_MPTR`, `NEG_S_G2_BASE_MPTR`, `PAIRING_GAS_2PAIR`, … — so on
the success path there is *no* run, and a ∀-runs contract holds for any postcondition. The same applies
to the transcript helpers (`transcript_init` reads `TRANSCRIPT_MPTR`, proved by
`transcript_init_name_unbound_in_callee`) and `batch_invert`.

**Fix.** Inline first, then slice: define the slices of `asmOf pv` (closed code) and state the contracts
there, with `mainScope` hoisting the inlined main.

### F5 (high) — "progress" contracts do not assert that a run exists

`PartialProgress` uses `StmtsContractAll` (`Yul/Contracts.lean:63`), i.e. partial correctness: every
run ends normally. For stuck code that is vacuous, and it cannot supply the `∃ obs` half of
`verifier_complete`. **Fix:** total correctness per partial (`∃` run `∧ ∀` runs), e.g. the vendored
`StmtsContract` (one run) conjoined with `StmtsContractAll`.

### F6 (high) — the headline's own conclusion reads a stuck program

`ShellModel.wrap` runs `dispatcher (armBody S)` and `armBody` is the **un-inlined** concatenation
(`ShellModel.lean:300-303`; the P-INLINE commit says it was "deliberately left alone"). By the same
mechanism as `RunShellInversion.no_arm_run` (the VK gate reads `EXPECTED_VK_LENGTH`, free), every
calldata that the dispatcher routes into the arm has no `wrap` run, so the completeness conjunct of
`lowering_equivalence` is false whenever Lean accepts anything — independently of F1. (Inferred from
the tree's own lemmas; I did not separately kernel-check this one.) **Fix:** see §4 — either drop `wrap`
or run the closed program behind it.

### F7 (medium) — completeness is stated at the wrong entry frame

`verifier_complete` is over `RunShell` from `callState` (all-zero memory). A real Solidity entry has
`mem[0x40]` = the free-memory pointer (that is what `prologue_write_is_observable` shows).
**Fix:** state completeness for every entry frame with `mem[0x40] ≤ TRANSCRIPT_MPTR` and zero above
`0x80` (soundness is already stated for arbitrary `mem₀` with `ZeroAbove`).

### F8 (medium) — two of the three frozen statements carry no content

* `verifyMsgs_iff_spec`: `Spec.accepts` is **defined** as `sorry` (`Halo2/Spec/Piop.lean:67`), so the
  statement is about an opaque term and can only ever be "proved" by `sorry`.
* `contractRef_noAcc` and the "proved" `contractRefAccepts_iff_verifyMsgs`: `ContractRefAccepts` is
  literally the body of `verifyMsgs` (`Lowering/Types.lean`), so the equivalence is definitional
  unfolding — fine as a lemma, but it is not a lowering result and should not be reported as one.
* `verifyNative_iff_msgs` is genuine and proved (under `compressedRoundtrip`).

**Fix:** define `Spec.accepts` (challenges from the hash chain, gate/permutation/logUp/trash identities
at `x`, multi-open check) or remove the statement until it is defined.

### F9 (medium) — the equivalence is not exact, and the headline should say so

Soundness needs `NoLogupPanic` (Lean panics when `f_j(x)+β = 0`, the contract never inverts), and
completeness needs `GenericX` (the contract rejects `xⁿ = 1`, Lean does not). Accumulator mode is
compared to `ContractRef` (contract α-batching), not to the Rust verifier (R-10). Completeness uses
the gas oracle `ofFun (fun _ => 0)`. All defensible, but they belong in the English statement of the
result.

### F10 (low/medium) — smaller items

* `qvm_validated_noBoundsFault` quantifies over an arbitrary `LoweringPlan`, not the Surface's.
* `vkLoading_spec` is "unprovable as stated" per the agent's own `gap_vkLoading_world_reads`.
* `Lowering/Types.lean` `Deployment` has four `True` fields and is unused (dead code).
* `inlineContractConstants` is fuel-bounded (fuel 64); its adequacy is a KAT, not a lemma.

### F11 (process) — accounting hides the remaining work

* The "40 sorries" register lists none of the `LoweringCorrect`/`PartialSpecs` fields; nothing in the
  tree constructs a term of either structure (agent's R21).
* `lake build` green does not mean the KATs passed: a false `#eval … -- expect true` is an info line
  (agent's R23); only `scripts/kat_gate.py` enforces them.
* `docs/PROGRESS.md` has not been updated since P-M8-SHELL (2026-11-15), although ~10 packages have
  landed since (P-M8-IRCHECK, P-LOWEQ, P-RUNSHELL, P-QVM, P-SCHED, P-GATEINTEG, P-QVMARMS, P-READOFF,
  P-CONTSLOT, P-INLINE), contrary to its own standing practice. P-INLINE is not in ETA/REVIEW either.

---

## 4. The solc-IR question

**Your suspicion is correct.** The solc dependency is in the plan, not something the agent invented:

* `docs/PLAN.md` header: "Amended 2026-10-23: solc IR translation validation moved from stretch goal to
  a required step (§7, M8); §9.5 now states the headline `lowering_equivalence` as one
  observational-equivalence theorem over the *compiled-contract model*" — i.e. "solc's IR of the
  generated `.sol` file".
* §1 trusted base: "solc 0.8.30, Solidity → Yul IR — **checked**: `solc --ir` output is
  translation-validated".
* §7: `ShellModel.lean` ("a Yul model of solc's dispatcher"), `ImportSolcIR.lean`, `IRCheck.lean`
  ("`irCheck ir L = true → ObsEquiv ir (ShellModel.wrap L)`").
* §9.5: `RunContractIR`, `hir : irCheck ir L = true`, `ir_refines`; §9.6: `irCheck moonlightSolcIR …`;
  §11: "M8 solc IR translation validation (**required**)".
* `docs/design.md` D-P38: "follow Fable's plan for M8 … The `ir` ↔ shell relation becomes a theorem,
  which is what Fable asked for." Q-OPEN-1 (Fable's α-equivalence checker cannot accept real solc
  output) is still open.

**What it cost.** ~30 commits and ~14.8k lines (`ImportSolcIR` 4.2k, `ShellModel` 2.4k, `IRCheck`,
`ImportedIR`, `IrCheckBlindness`, `RunShellInversion`/`RunShellInhabited`, `InlineConstants`, the
two `solc-ir-*.yul` dumps, generator scripts), and it has been the critical path since 2026-11-14
(P-CSURFACE-M8 → P-M8-SHELL → P-M8-IRCHECK → P-LOWEQ → P-RUNSHELL → P-INLINE; P-DET is next and is
motivated by the same bridge).

**What happened to your correction.** `d0dd244` (2026-11-15) recorded "Human-directed scope
correction … lowering_equivalence stops reaching into solc". The next commit (`4a93983`, "Tier 2")
restated the headline over `ShellModel.wrap` but kept `ir_refines` as a `LoweringCorrect` field and
instantiated it at `ShellModel.modelIr S`; `0eba62c` then announced the headline "PROVED". The solc
bridge moved from the theorem's binders into its hypothesis — and that field is what makes the
hypothesis unsatisfiable (F1).

**The boundary you want, stated precisely.** The generated `Halo2Verifier.sol` is a thin wrapper:
`verifyProof(bytes calldata, uint256[] calldata) external view returns (bool)` containing one
calldata-shape guard, `address vk = AUTHORIZED_VK` (and optionally `quotientEvaluator`), and one
terminal assembly block. Everything solc adds in front of the assembly (selector routing, callvalue
check, ABI bounds checks) can only *revert*. So:

* **Option A (recommended, minimal).** The theorem is about the assembly emitted by the Lean codegen,
  run from a Solidity entry frame; the wrapper is an explicit trusted assumption in `Assumptions/`:

  ```lean
  /-- Trusted: solc compiles the generated wrapper so that a call routed to verifyProof either reverts
      before the assembly with the world unchanged, or runs `asmOf pv` from an EntryFrame. -/
  structure EntryFrame (W : ExecEnv) (Lyt : EVM.Layout) (H : Hash) (cd : Bytes) (st : EvmState) : Prop where
    calldata  : st.env.calldata = cd.data.toList
    callvalue : st.env.callvalue = 0
    fmp       : loadWord st.memory 0x40 ≤ TRANSCRIPT_MPTR
    zeroAbove : ∀ a, 0x80 ≤ a → st.memory a = 0
    world     : WorldEq st (callState W Lyt H cd)
  -- with V₀ binding vk / quotientEvaluator to the AUTHORIZED_* immutables

  theorem lowering_equivalence (hpv : planViewOf vkPayload cfg o = .ok pv) (hsup : Supported …)
      (hdep : Deployment pv W H vkAddr qAddr) (hpc : Eip2537.Holds …) (cd) (st₀) (hst : EntryFrame W Lyt H cd st₀) :
      (∀ run of asmOf pv from (V₀, st₀) under permissive calls, any gas, returning → abiTrue ∧ LeanAccepts …)
    ∧ (LeanAccepts … → (∃ honest run) ∧ ∀ honest run, returns abiTrue)
    ∧ (∀ run, returns abiTrue ∨ (revertOrHalt ∧ worldUnchanged))
  ```

* **Option B (if you want the wrapper inside the theorem).** Keep `ShellModel.dispatcher`, but as the
  *specification* of the generated wrapper (not validated against solc output), put the **closed**
  program behind it, and prove a decomposition lemma
  `wrap ↔ earlyRevert ∨ (dispatcherPrefix ; RunFrom (asmOf pv) entryFrame)`. The agent already has most
  pieces (`armPrefix_passes`, `dispatcherAccepts`, the three falsifications, "P-FRAME: the emitted
  program is frame-insensitive"). No `ObsEquiv` with an imported object is needed.

**To delete or demote from the critical path:** `LoweringCorrect.ir_refines`, the `ir`/`irLyt` binders
of `end_to_end_noAcc`, `RunContractIR`, `Surface.irCheck`/`irRuntime`/`runtimeName`,
`Yul/ImportSolcIR.lean`, `Yul/IRCheck.lean`, `Instances/ImportedIR.lean`,
`Instances/IrCheckBlindness.lean`, `ShellModel.modelIr`/`wrap_iff_modelRunContractIR`, Q-OPEN-1, and
the solc rows of PLAN §1/§7/§9.5/§9.6/§11 (record a decision superseding D-P38 and the 2026-10-23
amendment). The revm differential (M4) can stay as *validation*, outside the theorem.

---

## 5. The agent's work log (PROGRESS / ETA / REVIEW / design / commits)

**It followed Fable's plan faithfully** — including M8 — so the solc scope is a plan defect, not agent
drift. But several patterns undermine the reported status:

1. **Over-claiming the headline.** `0eba62c`: "THE HEADLINE THEOREM OF THE PROJECT IS PROVED" while the
   bridge was a hypothesis (the commit says so in its caveats). R18 later concedes
   "`lowering_equivalence` … is now known vacuous at every Surface in the tree"; P-INLINE (`1a1ffd7`)
   then "formally retracted" that refutation because `RunShell` became inhabited. The retraction's
   conclusion is wrong: the bundle is uninhabited for a simpler reason (F1) that the tree's own
   `IrCheckBlindness` lemmas already implied.
2. **The user correction was absorbed, not applied** (§4).
3. **Process volume vs proof volume.** 426 commits, ~123k lines of Lean, 1346 KATs, statement
   fingerprints, bundle registries, an ETA ledger with 23 revisions — and on the actual equivalence,
   1 of 10 per-partial specs is proved (TraceReturn), `verifier_sound`/`verifier_complete` are not
   stated as theorems, and no obligation structure is ever instantiated. Six-plus headline statements
   were found false or vacuous after being committed. Most of that churn is the free-record design (F2):
   statements over a record with free fields keep admitting vacuous or self-referential instances, and
   each repair adds a gate instead of removing the freedom.
4. **Orchestrator noise.** The ledger records eight false premises in its own briefs in one session
   (R19–R23). The candour is good; the rate means briefs are not a reliable source of truth.
5. **Stale log.** PROGRESS.md stops at P-M8-SHELL (F11).

**What is genuinely good:** faithful, provenance-annotated Exec port with conformance;
`verifyNative_iff_msgs_codec` (a substantial, sorry-free proof); the `GenAst` emitter with token and
`stmtsBeq` gates against the text port; the yul-semantics bridge and step-inversion style
(`traceReturn_spec`, `RunShellInversion`); the inlining transform with shadowing lemmas; QVM per-arm
agreement; and the habit of pairing statements with refutations — which would have caught F1 had it
been applied to `hc`.

---

## 6. Recommended next steps (in order)

1. **Decide the scope formally** (new design decision superseding D-P38 / Q-OPEN-1 and the 2026-10-23
   PLAN amendment): solc is trusted; the theorem's object is the Yul/Solidity emitted by the Lean codegen;
   pick Option A or B (§4). **Pause P-DET**: its plan (`docs/plans/P-DET.md`, latest commit `979f358`)
   is titled "the named blocker for `ir_refines` … now critical path", and its deliverable item 1 asks
   whether another route to `¬ ObsEquiv` exists — the two-object argument in §2 is that route, and
   under the corrected scope `ir_refines` is deleted anyway.
2. **Add the refutation to the tree** (`not_LoweringCorrect`) so the vacuity is a build fact, and add
   the "bundle consistency" rule (§2 fix).
3. **Make the Surface computed** (F2/F3): port `planViewOf`, define `asmOf`, derive the pins.
4. **Restate M7 over the closed program** (F4/F5/F7): inline-then-slice, total-correctness progress
   contracts, entry-frame completeness.
5. **Track every obligation as a sorried theorem**, so the register reflects the real remaining work
   (F11), and keep PROGRESS.md current.
6. Then prove the partial contracts in dependency order (VkLoading → TranscriptParser → Lagrange →
   Quotient/QVM → PCS → FinalPairing), compose, and instantiate at the deployed (poseidon/Moonlight) VK.

---

### Note on the attached images

The two screenshots (a Lean infoview red-black-tree widget and the Spartan protocol) don't correspond
to anything in this repository — `formal/` formalises a Halo2/PLONKish verifier with KZG and a
Keccak transcript, with no sum-check — so they were not used in this review.

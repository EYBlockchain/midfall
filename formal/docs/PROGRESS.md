# Midfall formal - progress

Dated snapshot: 2026-10-28 01:24 UTC. Companion to `ROADMAP.md` (estimates and velocity) and
`REVIEW.md` (findings log, through R-55). This file records **where the work actually
stands**, what landed, what is blocked, and what is open with the human.

Normative plan: `docs/PLAN.md`. Proof programme: `docs/plans/P-SE-semantic-equivalence.md`
(2,300 lines; sections A-R hold the Lean statement sketches). Handover briefs:
`docs/plans/P-*.md`.

## Measured state

| | value |
|---|---|
| `lake build` | green, **3417 jobs** |
| `scripts/checks.sh` | green, exit 0 |
| Lean modules | **90** files, **74,006** lines, all reachable from `Midfall.lean` |
| Known-answer gates | **1090** `#eval ... -- expect` across 69 files |
| Theorems and lemmas | **111** (was ~20 at the start of this stretch) |
| Tracked sorries | **51**, every one registered with a named owning stage; zero UNOWNED |
| Frozen statements | `Statements.lean` hash OK; axioms `[propext, sorryAx, Classical.choice, Quot.sound]`, unchanged since M1 |
| Rust baseline | branch `formal/baseline`; **M0 tag still not cut** |

## The generator port: complete except three named gaps

**The headline result.** `renderHalo2Verifier` on a **derived** context equals the tracked
deployed artifact byte for byte - 175,908 bytes, 3,024 lines, no trailing newline
(`Instances/DeployedProfile.lean:533`, verified by the orchestrator). The only differing
line is the `BUILD_ID` constant, and the gate patches it explicitly rather than hiding it.

Landed in this stretch, in order: `VmValidator` (P-09e), `VmRecognizers` (P-09f),
`FoldTypes`/`FoldCompute` (P-10), `LoweringPlan` (P-11), `Evaluator` (P-09h),
`QuotientBlocks` (P-10c), `Evm`/`Calldata`/`Builder` (P-12), and the whole template layer
- `VerifierPartials`, `Contracts`, `Artifacts`/`DeployedProfile` (P-13a..f).

**Remaining port gaps, each named with its cause:**

1. **The circuit as data.** No Lean term produces a `LoweringPlan`. The blocker is *not*
   the memory constructor (that is ported and used) - it is that `Data.new`'s `ENC:432`
   assert refuses a default `ProtocolPlan`, so the poseidon `ConstraintSystem` as data is
   the gate. Publishing `(features, srs_fingerprint)` in a deployment record would retire
   the last transcription and close `BUILD_ID`.
2. **`blk` returns text, not ASTs.** P-13 ported templates as *renders*. Stage 4 added
   `Lowering/Partials.blk : Partial -> PlanView -> YulBlock`, so the seven spec theorems
   are statable; the per-partial **proofs** still need the real Yul ASTs from P-13's
   generated regions.
3. **`YulSemantics.SyntaxEq.stmtsBeq` does not exist.** Verified by grep over `Midfall/`
   and `vendor/`: only prose references. **D-P13 names it the authoritative structural
   equality**, so M3's structural acceptance and `render_eq_print`'s surviving conjunct
   both rest on an undeclared identifier. Needs defining, or D-P13 amended.

## P-SE proof programme: stages 0-4 complete, stage 5 running

| stage | content | state |
|---|---|---|
| 0 | baseline, `#check decodeAcc`, `SemanticEquivalence.lean`, CI script edits | **done** |
| 1 | `Yul/{Bridge,Contracts}`, `Assumptions/{Codec,Eip2537}` | **done** - `Contracts.lean` has **zero holes**, all 10 lemmas proved |
| 2 | `Lowering/{AccEncoding,Accumulator,VkDigest,Calldata}` | **done** - 1,977 lines, 23 holes registered |
| 3 | D6 Exec refactor + `Lowering/{Checkpoint,Snapshot,Inv}` | **done** - `Inv` satisfiable at all 7 checkpoints by computation |
| 4 | `Lowering/{Surface,Partials}` | **done** - **all seven `*_spec` theorems STATED**; fixture has 4 theorems proved, zero holes |
| 5 | `Lowering/{Qvm,QvmFold}` | **running** |
| 6 | `Lowering/Obligations.lean`, SORRY regen, axioms sweep | queued |

**Y-3 is resolved** - the open-dialect committed run exists, with determinism
*hypothesised* (`ExternalCalls.Functional` -> `dialect_deterministic` -> `Run.det`) rather
than assumed, and world-local call relations built in from the start per attack FIX 36.

**Why the headline theorems are not stated yet.** `ir_refines` and `lowering_equivalence`
were deliberately **not** written: their only run hypothesis `RunContractIR` is
uninhabited today, because `memoryguard`/`setimmutable` are absent from the vendored
dialect. Stating them would be the vacuity class. The `memguard` **bound** was recovered
without the AST (`Generator/Evm.lean:129` reads the free-memory-pointer initialiser from
the runtime bytes), so `DeploymentW.memguard` is a real decidable Prop - proved
satisfiable, refuted by a 0x2000 prologue.

## Five false-as-written statements found, not papered over

The instruction was: if a statement is false as written, stop and report (PLAN 12). It has
been exercised five times, each corrected by **strengthening** or by restricting with the
falsity recorded - never by weakening silently:

| # | statement | what was wrong | resolution |
|---|---|---|---|
| 1 | `end_to_end_noAcc` (PLAN 9.5) | RHS satisfied **vacuously** when no run exists - a `forall` over zero runs | run existence made an explicit conjunct (`1f4fba5`) |
| 2 | `countdown_or_halt` (P-SE A) | not derivable: `Step.loopLeave` yields `.leave`, `loopCondHalt` yields `.halt` at fuel 0 | rule inverts all 7 loop constructors, 8 hypotheses, 3-way conclusion |
| 3 | `decodeAcc_encode_pointPair` (P-SE F) | `.pointPair` rejects any non-empty fixed-base tail, so LHS is `none` | strengthened with `hfb : fb.size = 0`; falsity computed in a gate |
| 4 | `Inv_mono` (design0) | **false** given the binding `liveAt` fix - garbage-selector state satisfies `.pairing`, refutes `.quotient` | not stated; no `True := trivial` placeholder left |
| 5 | `main_concat` (P-SE N) | `main` has a prefix (AssemblyHelpers definitions), so it is not the concatenation of 7 slices | stated existentially: weaker and true |

Plus two known-false statements carried from earlier and now stated in their true forms:
`decodeAcc_injective` (over normalised `accWords`) and `decodeAcc_encode` (restricted to
`.pointAndScalar`).

**And one normative claim corrected by measurement:** PLAN 13 said instance words >= r and
trailing bytes *may be accepted*. P-12 measured the opposite from the tracked artifacts -
the decoder is **EXACT**. P-SE decision D7 was right; the risk note was the stale
artifact. `calldata_canonical` can be stated exactly.

## Recurring failure modes (worth keeping in view)

* **My briefs' scope claims have been wrong in every package** - line ranges, hazard lists,
  and once six whole files. The P-13 split enumerated 7 verifier partials where the
  directory holds 13, leaving 30.1% of the deployed artifact's bytes unassigned for four
  packages. Standing instruction now: re-measure, and gate 70 makes a 14th file a red.
* **Inherited claims go both ways.** One package reported a "live AND UNPINNED" defect that
  was **false** (`List.range'` takes a count, not an inclusive end - applying the fix would
  have introduced an off-by-one). The next reported a brace mis-port that was **true** and
  that its predecessor's own gate had pinned wrong. Rule: whoever acts on a claimed defect
  re-runs the measurement.
* **`Fr 17` is too small for magnitude, width or truncation gates** - `truncate` is the
  identity there. Bit twice for real (R-55); use `Fr 1009` or the real modulus.
* **Never perturb the working tree in place** (R-54). A killed harness left `.reverse`
  deleted from `MultiPrepare.fEval` - a semantic change that built clean and passed KATs.
* **`Instances/` confinement greps DIRECT imports only** (R-55), so a concrete model in a
  transitively-imported file stays invisible. Gates needing a model live in `Instances/`.
* **Multi-line anchored edits are my least reliable operation** - they deleted neighbouring
  lines ten times across three repairs this session, and once got committed before I
  noticed. Every catch came from running the tool, not trusting the edit.

## Open with the human

1. **Vendor dialect edit** (`memoryguard` + `setimmutable`) - D-P15 prerequisite. Blocks
   the AST-level IR import, i.e. `ir_refines` and therefore `lowering_equivalence`.
2. **`stmtsBeq`** - define it, or amend D-P13 to name a relation that exists.
3. **`Common/Bytes.lean` lemma** - `bytesToNatLE_natToBytesLE`. `Array.foldl` is not
   definitionally `List.foldl` in 4.35 and core exports no bridge. Gates two holes.
4. **Force-add untracked artifacts?** `Halo2Verifier.direct.sol` / `Halo2VerifyingKey.direct.sol`
   are the only bytes exercising the `quotient_direct` arms; the dump's `proof.bin`/
   `calldata.bin` gate three byte checks. Related: the tracked poseidon fixture set is
   internally inconsistent (4,752-byte tracked `proof.bin` vs the 2,640-byte dump matching
   the tracked `.sol`).
5. **F5 - the x3 error bound is unsound, not merely loose.** `chalMass` applies
   `s / 2^128` uniformly, but x3 is reduced into the field *before* truncation. For the
   six untruncated rounds the bound is pessimistic but sound; for x3 it is too small.
6. **F6 - ARSDH vs q-DLOG.** ArkLib's `function_binding` assumes ARSDH; PLAN 9.4 states
   S1/S3 against a q-DLOG game. Carrying an ARSDH term or supplying a reduction is a
   choice, not an oversight.
7. **M0 baseline tag** still uncut; `scripts/gate_negctl.py` still untracked.

## Next

1. Stage 5 (`Qvm`/`QvmFold`) - verify whether `IdentityCorrespondence` is now dischargeable,
   given P-09h and P-10c landed the Evaluator and `quotientExprFromPlonkExpr` after P-11
   declared it blocked.
2. Stage 6 (`Obligations`) - the headline structure. **Read sketch section Q (line 2164)
   and section R (line 2379) before briefing it**, not just the index entry.
3. Independent and unblocking: the vendor dialect decision (1 above), which is the only
   thing between stage 6 and a stated `lowering_equivalence`.
4. Per-task adversarial review remains **deferred** until the generator's semantic-
   equivalence results land, per the standing instruction. Note what that has cost: three
   of the five false-as-written findings above came from *later implementation packages*
   and one came from an external review - none from a scheduled review pass.

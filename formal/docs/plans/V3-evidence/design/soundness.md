<!-- Design memo behind PLAN-V3 (M3/M6 — the soundness architecture). Written by one design pass and kept as delivered, with local paths made repository-relative. Decision numbers inside predate PLAN-V3 §2 (D-P53 onward): follow that table. Where this memo and PLAN-V3 disagree, PLAN-V3 is the reconciled text. -->

# PLAN-V3 design memo - the soundness architecture

## 0. Provenance

- HEAD at start `6bde89f`, at end `6918991`. Four docs-only commits landed while I worked; `git diff --stat 6bde89f HEAD -- formal/Midfall proofs` is empty. The task named `f2fe99b`; `f2fe99b..6bde89f` is docs only as well. D-P51 is now taken (commit 5a8585e); the next free number is D-P52.
- Scratch directory: `docs/plans/V3-evidence/lean/soundness/`
  - `SoundnessV3.lean` (1451 lines, typechecks, 6 leaf sorries, all glue proved)
  - `RawDecode.lean` (stand-alone proof of the decode lemma, plus the fixture measurement)
  - `ExitMeasure.lean`, `PointSets.lean` (measurements)
- Marking: [T] = typechecked or evaluated at this tree; [R] = read in the source, not executed.
- Nothing in the repository was edited.

## 1. The problem, restated

`lowering_equivalence_of_blocks` (Blocks.lean:493) states every block contract relative to one final snapshot. For calldata on which Lean fails before a snapshot exists, "returns implies Lean accepts" rests on the sorried `Render.Rejects`, and conjunct 3 rests on `rejects_of_not_accepts`, which is false on the logup-panic set. Staged rejection exists only as a card title.

## 2. Two order mismatches that decide the design

These are why the obvious repair (digest I-2: simulate against `snapshotOfTrace .. snapshotOfPcs`) does not work as stated.

1. **Point validity is last in the contract and first in Lean.** `decodeSlots` (Calldata.lean:310) calls `ofEip?` on every G1 slot. The parser only range-checks (AssemblyHelpers.yul:94-104); curve and subgroup membership is established by G1MSM inside the PCS block (generator kzg/mod.rs:1826 fused final MSM, :1898 for pi; coverage enforced by kzg/mod.rs:723-740). So between `.transcript` and `.pcs` the contract does not know the calldata decodes, and no Lean prefix record exists at all for an invalid point. [T] `decodeCalldata_eq_raw` (proved) splits the decode into exactly these two halves.
2. **The parser writes x1..x4, fCom, pi before any algebra.** In Lean those are produced inside phaseA/B/C, after `linearize` (logup.rs:460 panic) and around `fEval` (kzg/mod.rs:479 panic). `Checkpoint.prefixNeeds .transcript = "snapshotOfPcs"` records this. A simulation keyed on `snapshotOfPcs` is circular: to show `fEval` does not panic one needs Lean's x3, which is only nameable after `fEval` succeeded.

## 3. Options considered

- **A. Keep BlockSound, decompose Rejects into staged rejection rows (PLAN-V2 M0.2).** Rejected. Two contract families, a case split on LeanAccepts in the composition, and conjunct 3 still has no true obligation on the logup set.
- **B. Simulate against the existing prefix records.** Rejected as stated, for the two mismatches above.
- **C. A total contract-order reference verifier (digest A-7).** The most principled, and the largest: a functional model of every block. Not required to close the headline. Design D is its skeleton (`LeanRaw` and `Mirror` are its byte level) and can grow into it.
- **D. Recommended.** A staged invariant with an unconditional raw part and a decode-relative Lean part, plus a transcript-only Lean prefix.

## 4. The recommended design

### 4.1 The Lean verifier staged in the contract's order [T]

`leanStage R H inst ms : Checkpoint -> Except Fault (Snapshot ..)` (SoundnessV3.lean:334), for one decoding `ms`:

| checkpoint | Lean function from the previous stage | faults it can raise |
|---|---|---|
| .start | none; raw fact `abiHeadOk` (decode guards 1-4) | selector, two ABI head words |
| .vk | none; raw fact `envelopeOk` (guards 1-7) | proof length word, instance count, calldata size |
| .transcript | raw: `rawDecode`. Per decoding: `snapshotXcriptRun` = `snapshotAlgebraRun` then `pcsReads` then `assertEmpty` | raw: non-canonical scalar, out-of-range G1 word, cursor, non-canonical instance. Per decoding: static only |
| .lagrange | + `snapshotLagrangeStep` (existing) | static only (circuit.rs:2510, mod.rs:511) |
| .quotient | + `linearizeFull` (new: `linearize` returning expressions, linCom, queries) | logup.rs:460 DYNAMIC; the rest static |
| .pcs | raw: the calldata decodes. `snapshotOf` | invalid point; DuplicatedQuery / set collapse at x = 0; kzg/mod.rs:479; static |
| .pairing | + `DualMSM.check` | Error.opening |

New Lean definitions, all real:
- `rawSlots`, `rawDecode`, `liftRaw` (decode without and then with `ofEip?`).
- `pcsReads` (the eight transcript operations of `multiPrepare` with the algebra cut out) and `snapshotXcriptRun`. The only datum that flowed from the algebra into the schedule is the number of point sets, taken from the layout: `R.nSets := R.plan.proofLayout.qEvals.itemCount`. Do NOT use `plan.meta_.numPointSets`: [T] it is 0 at the deployed plan while the layout has 3 q_evals (review finding 6, confirmed at the instance).
- `linearizeFull` with `linearize_eq_full` PROVED (`simp only [Verifier.linearize, linearizeFull, map_bind, map_pure, bind_pure]`). This fills the `Snapshot.lin` hole (D6 limit 1) without editing `linearize`.
- `padSnap`: a Lean prefix presented as a `Snapshot` with inert defaults in the fields not yet computed. This is a transitional carrier so that `Inv` is reused verbatim; see pitfall 3.

Proved Lean-only lemmas: `decodeSlots_eq_raw`, `decodeCalldata_eq_raw`, `decodeCalldata_isSome_iff`, `linearize_eq_full`, `leanAccepts_of_final`, `leanFinal_of_accepts` (the last two from the registered `snapshotOf_prepareMsgs`).

### 4.2 The staged invariant [T]

```lean
def StageInv (R : Render p G₁ G₂ Gₜ) (H : Hash) (vkAddr : U256) (cd : Bytes) (k : Checkpoint)
    {c : ExternalCalls} {g : ExternalGas} (V : VEnv (Bridge.Dialect c g)) (st : EvmState) : Prop :=
  Frame R H vkAddr cd V st ∧ VEnv.get V "success" = some (1 : U256) ∧ BaseInv R k V st ∧
    LeanRaw R cd k ∧ Mirror R cd st k ∧ Agree R H cd k V st
```

- `BaseInv k`: `Inv` at `.start` or `.vk` on `witnessSnapshot` (those arms read no snapshot field); `True` from `.pcs` on. Unconditional.
- `LeanRaw k`: `abiHeadOk` / `envelopeOk` / `(rawDecode ..).isSome` / `∃ ms instW inst, Decoded R cd ms instW inst`.
- `Mirror k`: between `.transcript` and `.quotient`, each commitment region and the REVERSED_EVALS window is the verbatim copy of its calldata section (`MirrorAt`). Unconditional.
- `Agree k`: `∀ ms instW inst, Decoded R cd ms instW inst → ∃ S, leanStage R H inst ms k = .ok S ∧ Inv R.E R.params k R.pv S V st`.

`Agree` is vacuous while no decoding is known. That is correct, and it is the rule that organises the proofs: anything a block needs before the PCS exit must live in `BaseInv`, `LeanRaw` or `Mirror`, never in `Agree`.

### 4.3 The simulation contract [T]

```lean
def exitSim (R) (q : Partial) (H) (vkAddr) (cd) (V') (st') (o) : Prop :=
  match q with
  | .traceReturn => o = .halt ∧ st'.halted = some (.ret, abiTrue) ∧ LeanFinal R H cd
  | _ => o = .normal ∧ StageInv R H vkAddr cd q.pre.next V' st'

def BlockSim (R) (q : Partial) (H) (vkAddr) (c) (g) (cd) : Prop :=
  StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => StageInv R H vkAddr cd q.pre V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨ exitSim R q H vkAddr cd V' st' o ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st')) ∧
    StmtsContractAll (D := Bridge.Dialect c g) (R.scope c g) (R.slice q)
      (fun V st => Poisoned R H vkAddr cd V st)
      (fun _ _ V' st' o => (o = .halt ∧ Reverted st') ∨
        (q ≠ .traceReturn ∧ o = .normal ∧ Poisoned R H vkAddr cd V' st'))
```

The four Blocks.lean section 6 properties are kept: closed slices in `R.scope`, the poisoned arm, facts through `Frame`, and totality through `BlockProgS` (4.6). The Lean fact leaves the program in the TraceReturn exit arm; that is what `slices_seq_sound` dropped.

Row wrappers:
```lean
def Render.SimContracts (R) (product) : Prop :=
  R.Valid → SimPins R → Eip2537.Holds R.E.g1 ⟨R.encG2⟩ product →
  ∀ H vkAddr cd, SoundSide R H cd → ∀ (q : Partial) (g : ExternalGas),
    BlockSim R q H vkAddr (permissive (callsOf product)) g cd
```
`SimPins` (four fields): the encoder-first compressed law (D-10, A-4), `eipRoundtrip`, `toEip 1 = 128 zero bytes`, and `hasMultiPointSet R = true`.

### 4.4 Composition, all PROVED [T]

- `seq_split`, `seq_final`, `seq7`: generic chaining over `++`.
- `slices_seq_sim`: seven `BlockSim`s give one contract for `R.slices` whose post is `FinSim` (revert, or ABI true together with `LeanFinal`).
- `run_split` / `run_join`: a committed run of the program is a run of `preBlock ++ slices` in scope, both directions, proved from `prog_slices_decomp`. Existential in the prefix endpoint, so no determinism is needed (digest C-3 option b).
- `soundness_of_sims`: conjunct 1. No case split on LeanAccepts.
- `rejects_of_sims`: what is left of `Render.Rejects`, as a corollary.
- `lowering_equivalence_of_stages`: the frozen `LoweringEquivalence R product` from `R.Valid`, `SimPins R`, `R.ExitOk`, `R.SimContracts product`, `R.ProgContracts product`. No hypothesis beyond the frozen headline's own side conditions.

Leaf register ([T], `#cone_sorries`):
- new: `snapshotOf_prepareMsgs, noWriters_prog, prog_slices_decomp, prefix_prog, prefix_sim, quiet_init, Run_worldEq_of_noWriters`
- old (`lowering_equivalence_of_blocks`): `noWriters_prog, prefix_run_clean, rejects_of_not_accepts, runBody_iff_slices, slices_seq_progress, slices_seq_sound, Run_worldEq_of_noWriters`, plus the hypothesis `hrej : R.Rejects product`.

The count is the same; what changed is that no leaf is known false, the monolithic hypothesis is gone, and three former leaves (the two sequencing lemmas and the run decomposition) are now proved.

### 4.5 Conjunct 3 without a snapshot [T]

`exitScan : Nat → Bool → Bool → Scan → Bool` is a fuel-bounded structural scan: no `ret`, `stop`, `selfdestruct` anywhere; `break`/`continue` only inside a loop; `leave` only inside a function. `Render.ExitOk R := ExitShape (R.preBlock 0 ++ R.slices6)`.

- `tr_exit_any` PROVED: from any state, every run of the TraceReturn slice halts, with a revert or with `return` of `abiTrue`. It reuses T.1's step lemmas plus a new `tr_guard_any` (the guard for an arbitrary value of `success`).
- `two_outcomes_of_exitShape` PROVED from the leaf `quiet_init`, `tr_exit_any`, and `worldEq_of_runBody`. It holds for any call relation and any gas oracle, with no SoundSide, no Holds, no LeanAccepts.
- Measured on the HEAD AST: the scan is false on the whole program, true once the last statement is dropped, the last statement is `ret`, and the TraceReturn slice is the last three statements.
- Measured on the Rust-rendered deployed verifier text: one `return(` (line 3021), no `stop`, `selfdestruct` or `invalid`, `leave` only inside `batch_invert` and `ec_pairing`.

`quiet_init` is the one new semantic meta-lemma: scanned code ends `normal` and not halted, or with a non-committing halt. It is the same `Step` induction `Run_worldEq_of_noWriters` needs; prove one generic per-op lemma and instantiate it twice.

### 4.6 One invariant or two? One.

`BlockProgS` is `StmtsTotal` under the honest calls with pre `StageInv q.pre` and post "normal and `StageInv q.post`" (TraceReturn: returns ABI true). The directions differ in the call relation, in the hypotheses on the calldata (LeanAccepts and CompleteSide versus SoundSide), and in the arms of the post, not in the boundary predicate. `slices_seq_prog` (both halves, using a new `stmts_append_run` / `total_append`) and `completeness_of_progs` (conjunct 2) are PROVED. Under LeanAccepts the decoding exists, so `LeanRaw` and `Mirror` are what let the honest run pass the parser checks, and `Agree` is what lets it pass the `scalar_inv` checks.

## 5. The fault-site table

Classification "static" means: depends only on the key, the plan and the layout, so it is discharged by `Valid` / `SimPins`. I classified by reading the main sites; the Exec port has 63 distinct `Fault.panic "..."` literals and 88 distinct site strings, and I did not machine-check each one. `lean_fault_table` (leaf) is the theorem that would.

| # | Lean site | class | owner block | contract check | status |
|---|---|---|---|---|---|
| 1 | decode guard: selector (Calldata.lean:334) | calldata | solc dispatcher | none in the body; `EntryFrame.selector` | trusted |
| 2 | decode guards: layout statics (:335-336) | static | - | - | `Valid.layout` |
| 3 | decode guard: ABI head words (:337-338) | calldata | prefix | contracts/Halo2Verifier.sol:148-152 | matched |
| 4 | proof length word (:339) | calldata | vkLoading | VkLoading.yul:101, :112 | matched |
| 5 | instance count (:340) | calldata | vkLoading | VkLoading.yul:102, :112 | matched |
| 6 | calldata size (:341, Nat) | calldata | vkLoading | VkLoading.yul:106-109, :112 (mod 2^256) | DIVERGENCE for size ≥ 2^256 (D-1): needs the EntryFrame bound |
| 7 | G1 words in range (decodeSlots :308) | calldata | transcriptParser | AssemblyHelpers.yul:94-104 | matched |
| 8 | G1 frame is a group element (decodeSlots :310) | calldata | pcs (poisons), finalPairing (reverts) | G1MSM: kzg/mod.rs:1826, :1898; FinalPairing.yul:86 | matched, but LATE; needs `Holds.g1Decodes` and the coverage invariant |
| 9 | proof scalar canonical (decodeSlots :315) | calldata | transcriptParser | TranscriptProofParser.yul:319, :382 | matched |
| 10 | cursor (:343) | static | transcriptParser | TranscriptProofParser.yul:416 | matched |
| 11 | instance canonical (:345; instOfWords? Shared.lean:106) | calldata | transcriptParser | TranscriptProofParser.yul:63, :68, :420 | matched |
| 12 | parseTrace invalidInstances x3 (Verifier.lean:112-118) | static | - | - | `SupportedV2.instShape` |
| 13 | transcript read errors in parseTrace, readAlgebra, phaseB, phaseC | static | - | - | needs `SimPins.compressedEnc`, the scalar round trip, schedule = layout |
| 14 | readAlgebra panics verifier.rs:348/366/370/410, arithmetic.rs:83 | static | - | - | key shape |
| 15 | lagrangeTriple panics circuit.rs:2510, mod.rs:511 | static | - | - | key shape |
| 16 | (contract only) x^n = 1 or x = ω^i in the window | hash | lagrange | Lagrange.yul:38, :93-98 | Lean accepts silently: CompleteSide |
| 17 | linearize: logup.rs:460 (Logup.lean:279) | hash + calldata | quotientLin | NONE (inversion-free helper identity) | SoundSide |
| 18 | linearize: other panics (mod.rs:532-536, logup.rs:422/443, trash.rs:70, permutation.rs:225/237, linearization/verifier.rs:84, verifier.rs:605-641, permutation/verifier.rs:173-178) | static | - | - | key shape; one is reachable at HEAD on imported keys (rotation equality, E-6) |
| 19 | phaseA addDummies | dead | - | - | `Features.solidity.outerFewerPointSets = false` [T] |
| 20 | phaseA DuplicatedQuery → Error.opening (Kzg/Utils.lean:148) at x = 0 | hash | pcs | `scalar_inv(0)`: kzg/mod.rs:1592 → AssemblyHelpers.yul:23, ONLY if some static point set has two points | NEW; pin `hasMultiPointSet` |
| 21 | phaseA point sets merge at x = 0 with no error (Utils.lean:137) | hash | pcs | NONE when every static set is a singleton | NEW; same pin, else a side condition |
| 22 | phaseA DuplicatedQuery / merge from value-equal commitments (MultiOpen.lean:42) | calldata | - | NONE | HEAD only; reference repair (E-1) |
| 23 | phaseA/B/C static panics (utils.rs:55-112, kzg/mod.rs:391, arithmetic.rs:173-313) | static | - | - | key shape |
| 24 | phaseB kzg/mod.rs:479, x3 in a point set (MultiOpen.lean:159) | hash | pcs | `scalar_inv`: kzg/mod.rs:1503, :1592 → AssemblyHelpers.yul:23 | matched; both reject, no side condition |
| 25 | assertEmpty (Native.lean:282) | static | - | - | dynamic only through row 21 |
| 26 | DualMSM.check false (Native.lean:292) | hash + calldata | finalPairing | FinalPairing.yul:88 → AssemblyHelpers.yul:294-307 | matched; needs `Holds.pairing2` and the base-point pins |
| 27 | (contract only) VK header checks, quotient VM guards, MF-2 guard | static / deployment | vkLoading, quotientLin, prefix | VkLoading.yul:67-70, :82-88; QuotientNumeratorBlock.yul:42-54 and the VM guards; Halo2Verifier.sol:189 | pins for completeness |
| 28 | (contract only) a precompile fails under permissive calls | call relation | any | AssemblyHelpers.yul:33-34, :296; `success := 0` then FinalPairing.yul:86 | revert or poisoned |

### The new divergence (rows 20, 21)

Rust and Lean deduplicate the opening points by value ([R] kzg/utils.rs:46-52, a HashMap keyed on the point; Kzg/Utils.lean:137). At x = 0 every rotated point is 0. [T] `xZeroCollapseKats_ok`: with a commitment opened at two rotations the result is `Error.opening`; with only single openings at two rotations, two point sets become one, so the read schedule shrinks by one q_eval and Lean then fails at `assertEmpty` or at the pi read. The contract's layout is static. It reverts at x = 0 only because `lbasis_j` contains `pt_j - pt_k` and `scalar_inv` reverts on zero, which requires a static point set with two points.

- [T] At the deployed plan the static sets are `[[0],[0,1],[0,1,-9]]`, so both sides reject at x = 0 and the decidable pin `hasMultiPointSet R = true` closes the row with no side condition.
- For a render with several point sets, all singletons, the contract has no check and can accept a consistent proof that Rust rejects. That case would need `x ≠ 0` in SoundSide (frozen surface). By argument only; not executed.

## 6. Where the side conditions enter, and what happens to the old objects

- SoundSide: a premise of `Render.SimContracts`, read by the `.quotientLin` row only. It is a soundness condition; the Blocks.lean:349-352 text calling it a completeness condition is wrong.
- CompleteSide: a premise of `Render.ProgContracts`, read by the `.lagrange` row only.
- `Render.Rejects`: delete as a hypothesis; derived (`rejects_of_sims`).
- `rejects_of_not_accepts`: delete (false); replaced by `two_outcomes_of_exitShape`.
- `BlockSound`: keep only as the internal shape of rows whose start checkpoint is `.pcs` or later, where a snapshot exists; lifted by `fp_blockSim_of_blockSound` and `tr_blockSim`. For vkLoading, transcriptParser, lagrange, quotientLin, pcs: write `BlockSim` directly.
- `BlockProgress`: replace by `BlockProgS`; `tr_blockProgS` shows the lift.
- `slices_seq_sound`, `slices_seq_progress`, `prefix_run_clean`, `runBody_iff_slices`: delete; replaced by proved lemmas and the two prefix leaves.
- Keep: `prog_slices_decomp`, `noWriters_prog`, `hoist_prog_addr_indep`, and every transport lemma of Blocks.lean:370-471 (all are used by the new glue).

## 7. Migration

- TraceReturn: `tr_blockSim` and `tr_blockProgS` are PROVED in the scratch file from the existing lemmas, with no new semantics. `tr_blockSim` needs no pin; `tr_blockProgS` keeps `trRetMptr`.
- FinalPairing: `fp_blockSim_of_blockSound` PROVED. It needs the poisoned half as a separate snapshot-free hypothesis, so FinalPairing.lean must export that half without a snapshot argument (restatement only).
- VkLoading: sections 1-4 (slice form, site inversion, fail helper, assign inversion) survive verbatim. The three gaps are restated over `StageInv`. Two things get easier: no decode hypothesis is needed (digest D-8), and the calldata-length clause of `Inv .vk` comes from the block's own `calldatasize` check. One thing is exposed: that check is modulo 2^256, so the row needs `cd.size < 2^256`.
- `Frame`, `Poisoned`, `Render.slices`, `Render.preSlice`, `Render.mainLocalsInlined`: unchanged.

## 8. How Inv must change (digest D-5)

1. Take the Lean value through a prefix, not the final snapshot. Transitional: `padSnap`. Target: prefix records, with x1..x4, fCom, pi in a transcript-level record (`SnapXcript`).
2. Missing clauses, now defined in `MirrorAt` against calldata: lookup-m, perm-z, lookup-helper, lookup-z, trashcan commitment regions, and the REVERSED_EVALS window. No `EvalRead → Fr` bridge is needed in the invariant: the window is the evals section word for word, and relating that section to Lean's arrays is an ALG lemma about `decodeCalldata` and `readAlgebra`.
3. QUOTIENT_EVAL_MPTR and SELECTOR_ACC_MPTR: the two inert `Inv .quotient` clauses become live once `lin` is filled, which `leanStage .quotient` does through `linearizeFull`.
4. Still missing and owned elsewhere: the payload's fixed and permutation commitment words against `R.vk` (D-6), the G1/G2 base slots, `E.delta`.

## 9. Pitfalls and guidance for the implementer

1. Never put a fact that is needed before the PCS exit inside `Agree`.
2. `leanStage` recomputes each stage from scratch. Rows need field agreement between stages, not only existence. Strengthen `leanStage_prefix` to `leanStage_agree` (the padded prefix equals the later stage on the prefix fields) in the same ticket.
3. `padSnap` is safe only while `InvAt k` reads prefix-k fields. Add a perturbation KAT: changing a padded field does not change `InvAt k`.
4. Prove each block row in two layers: SEM (the block computes a stated function of its input memory, or reverts) and ALG (that function agrees with the Lean stage). The parser row needs the ALG half five times in one shape: "if the Lean prefix exists, its transcript is the plan's schedule".
5. The PCS row carries the new obligation "normal exit with success = 1 implies a decoding exists". Its ingredients are `Mirror`, the G1MSM coverage invariant, `Holds.g1Decodes` and `decodeCalldata_isSome_iff`.
6. `lean_fault_table` is false at HEAD. It is the acceptance test of the reference repairs (E-1, E-6); do not schedule its proof before them.
7. `R.scope` hoists the helpers only (digest D-4). The scratch file keeps it so the TraceReturn lemmas apply. When the scope becomes the hoist of the whole program, `fail_lookup` is the one lemma to re-prove.
8. Names: `Inv` is ambiguous with `_root_.Inv` (write `Midfall.Lowering.Inv`); `calldataOf` is ambiguous between `LoweringV2` and `Lowering`; a `Render.foo` defined inside another namespace needs `_root_.Midfall.LoweringV2.Render.foo`; `if_true` is deprecated (`ite_true`).
9. The exit scan is structural in the fuel; small cases close by `decide`. At the deployment use the computable faces (`poseidonPv`, `poseidonM`) and fuel 100000.

Please review this memo for accuracy and completeness before relying on it.

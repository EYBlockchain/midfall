# STATUS - midfall

## 1. Verified at `077a3c5` - PROGRESS
**No full `verify.sh` has been run this session.** (o) = orchestrator-printed, (c) = worker-printed.

    root lowering_correct .... 2 sorried leaves (c, LH c1bb557): lowering_correctW, model_quotientMode
                               ROOT NOT YET RE-KEYED - that is WP A0
    root lowering_sound ...... not yet reported (WP A0)
    block rows ............... 0 INTEGRATED of 7
    exhibits ................. 2 PRESENT of 4 (c, T3.11)
    ValidV3 at F1 ............ NOT INHABITED; blocking clauses = generated (REFUTED at F1, but
                               SATISFIABLE per B4) + payload point half (OPEN, B3 ticket)
                               clause table 5 PROVED / 1 HALF / 1 REFUTED (c, OBJ.9 + R.7)
    root lowering_correctW ... not yet reported (WP C0)
    root generator_correct ... not yet reported (WP D2)
    outside the cones ........ register 91 rows / 22 ROOT (o, regenerated post-merge); V2 cone 10/1 REFUTED (c)
                               KAT 1633/118 (o, pin verified post-merge); fingerprint 14,109/0x3149ae4f... (c)
    reference gate ........... MERGED (B2, 077a3c5): nativeReplay_ok true, 21 checks, 0 failures
    full verify.sh ......... KILLED, VERIFY_EXIT=143 SIGTERM (o) - NOT a pass

**CORRECTION, and it is mine: the full `verify.sh` I ran after merging A0 was KILLED -
`VERIFY_EXIT=143` (SIGTERM), not 0.** The background job reported "completed, exit code 0"
because my wrapper's `echo` ran after `verify.sh` died; the log ends mid-`assert_axioms` output
and never reaches `cone_report` / `sorry_sweep` / `block_coverage`. **Cause: I ran full
`verify.sh` in the main tree while A3 was starting a ~50 min cold `lake build` in another
worktree - the prompt's OPERATIONAL section says explicitly not to run two gates at once. I broke
my own rule and then misread the wrapper exit.** A0 is not in doubt on the evidence that DOES
exist (worker printed `lake build` green, `verify.sh --quick` exit 0, `checks.sh` exit 0 at its
commit; I regenerated and cross-checked the register myself at 90 rows / 22 ROOT / 0 UNOWNED /
1 REFUTED, frozen hashes verify) - **but the full-`verify.sh` PROGRESS block is still not sourced,**
so it must be re-run with no other gate in flight before any number below is called a verify.sh
copy.
**KAT VERIFIED at `444df14` (round 143).** After a plain `lake build` (5293 jobs, green),
`python3 scripts/kat_gate.py` printed:
`ok: 1633 annotated known-answer checks pass across 118 files (both pinned: 1633 and 118)` - exit 0.
**An earlier attempt was RED (`KAT_EXIT=1`)** with `NativeReplay.lean` missing an object file,
`ChallengeStream.lean` failing to elaborate and `poseidonPermutationQueries` returning false.
**All of it was the damaged `.lake` left by the SIGTERM'd `verify.sh`, not a regression.** Two lessons,
both already in the prompt and both worth repeating: a killed build silently corrupts `.lake` and
produces false gate reds; and `kat_gate.py` needs `ELAN_HOME=$HOME/.elan` plus
`PATH=$HOME/.elan/bin:$PATH` exported or it cannot find `lean`. The same clean build re-printed
`NativeReplay.lean:432:0: []` - B2's reference gate still reporting zero failures on the merged tree.
## 2. In flight
- **A3** (vkLoading INTEGRATED, calibration B) - /Users/julian/midfall-b - t/A3 - since 18:55 - 8 h strongest
- **B2** MERGED at 077a3c5. One slot free: B1 (4 h Sonnet) or C1 (8 h strongest) are READY.
  WIP: cdb9da2 REF.2, 1a9a093 REF.1, fe9507f REF.4/5/8, 1a47c35 register+pins
- Preserved, not running: t/ST.13 at f71105d - monotonicity chain, DOES NOT BUILD; A2 absorbs it.
  Do not trust its 'PROVED (ST.13)' comment.

## 3. Next READY, per track
- **A**: A1, A2, A3 all after A0 - nothing on track A starts until A0 merges.
- **B**: B1 (4 h Sonnet) READY; B3-B6 after B2.
- **C**: C1 (8 h, F2 + widened clause table) READY - but D-P75 caps at two workers, so it waits.
- **D**: D2 after B1, B2.

## 4. Waiting on human
1. **REF.5g gate pairing** - check_frozen_axioms.py hard-requires the five D-P36a axioms, so
   retiring them (B2's REF.5 step 2) reddens that gate. **Blocks B2 completeness, then B3.**
2. **OBJ.11 needs cargo and a decision under R.5.** **Blocks B2's OBJ.11 item.**
3. **R.6 needs a Statements.lean re-hash**; PLAN-V3 marks it subsumed at ST.6. **Blocks nothing on
   A; confirm it is genuinely closed.**
4. **DG.7 CI branch permission.** **Blocks nothing on the shortest route** - negative control can
   be done locally.
5. **exitScan canonical form** - **owned by SIM.3 (A2), not a human item**; listed only because I
   mis-escalated it.
6. **Stale frozen prose** LoweringV2/Statements.lean:85-92 / :1037-1039 (says the refutation runs
   through supported; it runs through generated since R.7). **Batch into the next re-hash.**

7. **REF.6 Do 2 vs `PoseidonCoherence.lean`** - setting `poseidonE := <g1CodecC, ...>` falsifies three
   existing `rfl` pins the card omits from Needs (`:427`, `:433`, `:454`). A D.2 coherence change needing
   a decision, not silent absorption. **Blocks: B4 (ValidV3 at F1).**
### REF.5g - STOPPED CORRECTLY, not a blocker for the shortest path (round 140)

**My error, ninth instance: I told REF.5g the five D-P36a axioms were unused and the gate edit was
'follow-through'. I had not checked.** They are still declared as `axiom` at
`Midfall/Assumptions/CurvePairing.lean:69,74,81,88,101` (that file's only commit is `5a10e21`), and
`Instances/HoldsFinal.lean:57-58` uses `blsGT` as the `G_t` carrier via the axiom-built instance at
`CurvePairing.lean:103`. Eight further sites name them, and three hard pins were NOT on the card's Needs:
`Midfall/Tools/ConeReport.lean:89-94`, `scripts/DoneTest.lean:41-43/66-68/118-120`, and PLAN.md section 1.
**B2 landed REF.5's construction (077a3c5) but NOT REF.5 Do step 2, the deletion - so REF.5g's precondition
is unmet and emptying `HOLDS_EXPECTED` would assert a trusted base the tree does not have.**

**WHY IT IS OFF THE SHORTEST PATH ANYWAY: the V3 root does not depend on those five axioms.**
`assert_axioms lowering_correct` prints `ok (4 named, 0 native)` - standard three plus `sorryAx`. The five
are pinned in the V2 root, which D-P74 item 3 already reports RETIRED. **So completing REF.5 is a
trusted-base cleanup for the final claim, not a step toward `lowering_correct`.** REF.5g's patch is kept
uncommitted in /Users/julian/midfall-c with a write-up at /tmp/REF.5g-pending.md, and its recommendation -
land the gate artefact in the SAME commit as REF.5 Do step 2, definition-ising the five names so
`holds_exhibited` becomes standard-three without a HoldsFinal edit - is recorded for when it is picked up.

**LESSON, FOR ME AND FOR CARDS: when a gate asserts an axiom list, `grep -rn` for the axioms themselves.
Do not read a card's Needs and trust them. I asserted a fact about the tree from a card's prose, and a
worker had to stop me.**


**REF.5g FINAL, and it narrowed the remaining work to one file.** The gate's own words prove the five are
live: unmodified `check_frozen_axioms.py` exits 0 printing `ok: D-P36a probe - holds_exhibited depends on
exactly [Classical.choice, bls12_381Pairing, blsGT, blsGT_group, blsGT_module, blsGT_primeOrder,
Quot.sound, propext] ... and 8 exhibit halves carry no sorryAx`; with the allow-list emptied it exits 1
with `FROZEN STATEMENT AXIOMS BROKEN (5)`, one per constant.

> **Measured: `holds_exhibited_noAxiom`, `holds_exhibited_C` and `pairingC` are ALL on the standard three.**
> **`holds_exhibited` is the only theorem still pulling the five, and only because of an INSTANCE CHOICE at
> `Instances/HoldsFinal.lean:57-58`.** **So the distance from this tree to an empty allow-list is one
> instance, not a refactor.**

**Corrected dependency set: SIX files, not the three on the card** - add `scripts/DoneTest.lean:41-43,
66-68, 118-120` (three `#guard_msgs` fixtures, one pinning `ok (9 named, 1 native)`),
`Midfall/Tools/ConeReport.lean:89-94`, and `docs/PLAN.md` section 1. **Paths are `formal/scripts/...`, not
`scripts/...` from the repo root.** **Preserved artefacts: `/tmp/REF.5g-allowlist.patch` (44+/26-,
`git apply --check --reverse` passes) and `/tmp/REF.5g-pending.md`, whose sections 4 and 6 hold the drafted
registry-record change spanning `ObligationsGates.lean:650-693`+`:716` and
`check_hypothesis_bundles.py:110,124-135,155` - deliberately NOT done, since a partial move reddens both
the Python gate and `lake build`.** **Other gates it printed green: check_hypothesis_bundles (8 bundles /
7 exhibited / 23 spec bundles), check_statement_fingerprints (375 fragments), verify.sh --quick with
`assert_axioms lowering_correct` AND `lowering_sound` both `ok (4 named, 0 native)`.**

7. **PG-VKMEMORYFIT - THE CLASS IS TOO WIDE, AND THIS IS THE CRITICAL PATH.** A3b proved
   (`wrap_breaks_payload_clause`, `[propext, Quot.sound]`) that a render with
   `ptrAddr pv.memory.vkMptr >= 2^256` copies to the WRAPPED address, exits `.normal` with `success = 1`,
   and satisfies NEITHER `Inv .vk` NOR `Poisoned`. `ValidV3` bounds calldata length, the transcript
   region, the g1 floor and neg-Lagranges, but NOTHING bounds a memory address or a payload size. So
   `vk_blockSim` is FALSE for some valid render. **Options: (1) derive fit1/fit2 from the `generated`
   clause - no frozen change, PREFERRED and flagged viable; (2) add a `memoryFitB` conjunct to
   `programOkCore` - needs a signed decision AND one of W15's five re-hashes (three spent: ST.4, ST.6,
   OBJ.8); (3) state the row with the bound as a hypothesis - REFUSED on the record.** Once ruled, about
   1 h of reassembly closes `vk_blockSim` from what is already proved.
   **Blocks: A3 (then `vk_blockProgS`), and by extension A4-A12.**
8. **PG-SHADOWDECOMP - THE CONE'S DECOMPOSITION LEAF IS THE V2 STATEMENT, AND IT NEEDS THE FACT
   ONLY `prog_slices_decompV3` CARRIES (WP-A2, measured at `444df14`).** The root cone prints
   `Midfall.LoweringV2.prog_slices_decomp` (`LoweringV2/Blocks.lean:234`) and NOT
   `Midfall.LoweringV3.prog_slices_decompV3` (`LoweringV3/Statements.lean:244`). The V2 text is
   stated for a GENERIC render with no side condition:

   ```
   theorem prog_slices_decomp (R : Render p G₁ G₂ Gₜ) (vkAddr qAddr : U256)
       (c : ExternalCalls) (g : ExternalGas) :
       R.prog vkAddr qAddr =
           R.preSlice vkAddr qAddr ++ R.helpers ++ R.mainLocalsInlined ++ R.slices ∧
         [hoist (Bridge.Dialect c g) (R.prog vkAddr qAddr)] = R.scope c g
   ```

   Conjunct 1 is `inline (A++B++C++D++E++F) = inline (A++B++C) ++ inline D ++ inline E ++ inline F`,
   which is `Inline.inline_append` at five cuts, and whose third cut's left block ends in
   `mainLocals` - the two statements that bind `r` and `success` at top level. `constTableOf`
   filters exactly `vk` and `success` out of the table (`LoweringV2/Program.lean:59-63`), so a model
   whose rendered `Constants.sol` declares a constant named `r` (or `quotientEvaluator`) makes the
   equation FALSE, not merely unproved: the slices' reads of `r` are substituted on the right-hand side
   and left free on the left. That is findings B-5/D-13, and it is why ST.11 restated the leaf with
   `hns : noShadowB R = true`. **The hypothesis is not missing from the tree - `programOkB` carries
   `noShadowCore pv m` and `noShadow_of_programOk` projects it from `ValidV3.program`; it is missing
   from the V2 STATEMENT.** So the closure is a re-point, not a proof: `run_split`
   (`LoweringV2/Stages.lean:528`) and `run_join` (`:552`) are the only consumers of the V2 leaf,
   they live in A1's file, and each holds the `ValidV3`-class facts needed to feed
   `prog_slices_decompV3 R hns vkAddr qAddr c g`. **Blocks: the cone's `prog_slices_decomp` row, and
   it needs `inline_append` (GEN.4, registered, cone `-`) proved first. WP-A2 did not reach it inside
   its box; the goal state above is the exact one.

   **GEN.4 CLOSED THE `inline_append` HALF (this work package, on `t/GEN4`).**
   `Midfall.LoweringV2.inline_append` (`ProgramLemmas.lean:31`) is PROVED - statement unchanged, no
   hypothesis added to `ValidV3`/`ValidW`, axioms `[propext, Classical.choice, Quot.sound]`, no
   `native_decide`. It rests on `Midfall.Lowering.Inline.inlineScan_append`
   (`Lowering/InlineConstants.lean`, the threaded accumulator fact: `foldl_stepAcc_sh` +
   `foldl_stepAcc_blks_split` + `List.foldl_append`) and on `Inline.inlineScan_irrel`, which is the
   projection the shadow condition was always meant to do: a shadow list naming no constant is inert,
   so `topBinders a` collapses to `[]`. TWO PROVED FALSIFIERS, both by `rfl` on a hand-written
   observation (`SyntaxEq.stmtsBeq` is compiled through `WellFounded.fix` and does not kernel-reduce,
   measured): `Inline.inlineScan_append_is_threaded` (the unthreaded scan equation is FALSE) and
   `inline_append_needs_h` (this statement with `h` dropped is FALSE) - the B-5/D-13 `r` hazard,
   exhibited rather than asserted. **WHAT REMAINS IS THE RE-POINT, AND IT IS NOT A CONE DROP ON ITS
   OWN.** `run_split`/`run_join` (`LoweringV2/Stages.lean:528`/`:552`) still cite the V2 leaf, which
   stays FALSE for a valid render until they do not. The V3-side twin must live where the import is
   legal (`PrefixV3.lean`, A1b's pattern) and take `hns : noShadowB R = true` projected by
   `noShadow_of_programOk` - `Stages.lean` may NOT import `LoweringV3`. Because `prog_slices_decompV3`
   is itself still a sorry, the re-point MOVES the ROOT row from the V2 leaf to the V3 leaf and leaves
   both cones where they are (A1b's measurement, re-confirmed by this card: `inline_append` alone moves
   neither cone, its register row was cone `-`). The count drops only when ST.11 proves the V3 text;
   the `inline_append` ingredient is no longer missing, and what ST.11's own note lists besides it -
   `List.filterMap_append` for `hoist`, `hoist preSlice = hoist mainLocalsInlined = []` - are emitter
   facts, not shadow facts.**

    **ST.11 CLOSED THIS ROW (this work package, on `t/ST11`, base `c180a63`).`**
    `Midfall.LoweringV3.prog_slices_decompV3` is PROVED - `[propext, Classical.choice, Quot.sound]`,
    `#cone_sorries` 0, no `native_decide`, no new hypothesis on `ValidV3`. The proof reads the shadow
    condition off the FLAT un-inlined program once (`noShadowCore` scans every top-level binder, so
    every cut of the thirteen-piece block satisfies `inline_append`'s side condition), applies
    `inline_append` at all twelve cuts by one list induction (`inline_append_many`), then pushes
    `hoist` through `++` with `List.filterMap_append` against a new fact: the inliner rewrites a
    statement IN PLACE and so creates no top-level `funDef` (`hoist_inline_nil`, giving
    `hoist (preSlice) = hoist (mainLocalsInlined) = []`). The card said five cuts; that was the
    pre-OBJ.2 shape - it is twelve.
    **AND THE RE-POINT HAPPENED.** `run_splitV3`/`run_joinV3` (`LoweringV3/PrefixV3.lean` section 5)
    are A1's two lemmas with the SAME statements (`scopeV3 R c g` is `R.scope c g` and `slicesV3 R`
    is `R.slices` by `rfl`), proved from the V3 text with `noShadowB` PROJECTED by
    `noShadow_of_programOk (programOkB_of_valid hR)`; `Composition.lean` and `Totality.lean` now
    cite them. `Stages.lean` was NOT touched - no forbidden import, A1b's pattern.
    **THE TWO ROOT CONES MOVED: `lowering_correct` 19 -> 18 and `lowering_sound` 9 -> 8**, and the
    register is 87 -> 86 data rows / 19 -> 18 ROOT: one row REMOVED (`prog_slices_decompV3`, proved)
    and one row ROOT -> `-` (`LoweringV2.prog_slices_decomp`, now unreachable from both roots). The
    V2 text is still a sorry and still FALSE for a shadowing render; deleting it is a V2-side edit
    (`LoweringV2/Blocks.lean` cannot import `LoweringV3`), not this card's. The header block above
    is the pre-ST.11 `verify.sh --report` output and moves at the next report.

9. **PG-WORLDEQ (ST.10/SIM.3): `twoOutcomes_of_exitDiscipline` is one Step induction behind a
   second registered hole.** Its conclusion is
   `(⟨stObs, o⟩ : Obs).view = returnView st₀ ∨ (isRevertOrHalt ∧ worldUnchanged st₀)` and BOTH arms
   read `WorldEq st₀ stObs` (`returnView` is st₀'s own world with the halt set), so the leaf is not
   reachable without `Midfall.Yul.Bridge.Run_worldEq_of_noWriters` (`Bridge.lean:1221`, registered
   OPEN, cone `-`, "removed by V3 SIM.5 - the shared Step induction (ST.10 cites it)"). Its own
   docstring prices it: subterm closure of the fuel-bounded scan plus the per-op table over the ~70
   local ops and `finishCall` for staticcall - "the same 77-constructor cost class as
   dialect_deterministic". WP-A2's box went to ST.12; this row is NOT closed and no hypothesis was
   added to the leaf. **Blocks: the cone's `twoOutcomes_of_exitDiscipline` row, hence
   `twoOutcomes_of_scans`, hence conjunct 3 of both roots.**

10. **`snapshotOf_prepareMsgs` is a REPLAY-EVIDENCE obligation, not a Lean one (WP-A2: read, not
    proved).** `Midfall/Lowering/Snapshot.lean:380`'s own docstring says the `.ok` half is an unfolding
    plus a case split on the collapse, while the `isOk` half "additionally needs that no phase this
    file runs can fault where prepareMsgs succeeds, which is a claim that the Exec refactor is a cut
    and not a reordering (rule R1), and that claim is exactly what the D6 KATs and the conformance
    replay evidence, not a Lean proof". It is the cone's oldest ROOT row (since `a2557e7`). WP-A2
    records it rather than inventing a hypothesis: the fact nothing supplies is that the Exec refactor
    is a cut and not a reordering, and the tree's evidence for it lives in `Instances/`, which D-P71
    keeps out of this cone. **Blocks: 1 ROOT row of both roots; needs a decision - accept the replay
    gate as the evidence and retire the row, or port `prepare`'s schedule onto the phase records.**

**ITEM 7 CORRECTED TO ITS DEFENSIBLE FORM (VKFIT, proved negative).** I had written that `vk_blockSim`
"is FALSE for some valid render". **VKFIT could not exhibit a render (that needs WP B4), so existence is
NOT proved. The defensible statement is: `vk_blockSim` is NOT PROVABLE from `ValidV3` as written, because
`ValidV3` carries no bound that would make it true.** Recorded in `VkClean.lean` section 5b.

**fit1/fit2 are settled as a genuine human decision, with 15 new sorry-free lemmas**
(`MemoryPairs.lean` section 10, cone 0, axioms within the standard three):
- `ofNat_toNat_iff_lt` reduces them to plain bounds: fit1 <-> `ptrAddr R.pv.memory.vkMptr < 2^256`,
  fit2 <-> `R.pv.vk.len < 2^256`. **Nothing weaker can close the row.**
- **Route 1 (arena chain) REFUTED** - `new_vkMptr_image_unbounded`, `generated_face_allows_fit1_to_fail`.
  `VerifierMemoryLayout.new` does NOT emit `vkMptr`, it copies its argument (`new_vkMptr` is `rfl`), and
  `ptrAddr_valueFromNat` makes `ptrAddr` surjective onto `Nat`. **My brief's premise that every emitted
  `ptrAddr` is a sum of small literals was simply false - that is what made route 1 look viable.**
- **Route 3 (payload length) REFUTED** - `extendVk_len`, `vkLen_unbounded`, `fit2_can_fail`; and
  `vkCarriesBuild_extend` proves the ONE payload gate on the ok-path (`PlanNew.lean:773`) is INVARIANT
  under padding the constant table. **OBJ.4's `runtimeBytes.size = vk.len + 1` is an equation between two
  unbounded Nats, not a bound.**
- Route 2 was already refuted by LAYOUT (`layout_windows_not_tied_to_the_map`).

> **THE SENTENCE FOR THE HUMAN: the tree CAN bound a layout pointer from above - `transcriptMptr_lt` does,
> via `validate`'s `fixedLowMemory` loop - but it cannot reach `vkMptr`, because `new_transcriptMptr_eq`
> emits the LITERAL while `new_vkMptr_eq_arg` emits the ARGUMENT. `vk_mptr` is the eighth pointer, the
> reservation loop's output (`VK:535-544`), and `validate` ties it only to `scalarInvScratchMptr`, which
> `new` builds from the same `vkStart` - a tautology, not a bound. ROOT CAUSE IS FAITHFUL-PORT RULE R5:
> `usize` became `Nat`, and a 64-bit `usize` cannot wrap a 256-bit word.** **That is a real Lean/Rust
> divergence in the model, not a missing lemma.**

**Only STATUS option 2 remains: a `memoryFitB`-style conjunct on `programOkCore` - a frozen edit needing a
signed decision plus one of W15's two remaining re-hashes.** VKFIT did NOT add it, did NOT state the row
with the bound as a hypothesis, and left `fit1_of_bound`/`fit2_of_bound` ready so whoever signs it gets
A3b's ~1 h of reassembly. **Gates: verify.sh --quick exit 0 x3; cones 18/8 unchanged (correct - the row did
not close); register 86/18 with `git diff SORRY.md` EMPTY; KAT 1633/118 ran clean, which is also the
fingerprint assertion.**
## 5. Last three merges
- 077a3c5 B2 - reference gate green (nativeReplay_ok, 21 checks, 0 failures); a section-6 gate met
- 930c33c A0/PL.H0 - root lowering_correct UNREACHABLE/10 -> 22 OPEN leaves, native 0; ROOT re-keyed
- 1f2fd09 correction - post-A0 verify.sh was KILLED (143), not a pass; re-run with no gate in flight

---

## Standing notes (do not re-learn)
- **Plain `lake build` only.** `ram_guard --limit 6G` is KILLED (peak 11.8 GiB) and leaves `.olean`
  files missing -> FALSE red on the register.
- **Workers run `verify.sh --quick` + Accept commands, NEVER full checks.sh/verify.sh (W9).**
- **`lake env lean FILE` ignores lakefile options (`autoImplicit = false`): take numbers only from
  `lake build`, checks.sh, verify.sh.** Most of my session's axiom probes used it.
- **Seed the 3 untracked F1 fixture binaries into every worktree before its first brief**, or the 4
  Calldata.lean KAT arms fail (Calldata.lean:306-310).
- **`norm_num` refuses 2^280/2^336** (threshold 256); **no List.get?/eq_of_getEq/get_map/
  map_congr**; **`data` is a keyword** where YulSemantics.Syntax is imported (`{ ev with <<data>>
  := ... }`); no `match` or nested structure-update inside a structure-update field.
- **`g1CodecZ` is noncomputable (`ofEip?` is a `Classical.choose`), so the 5 point fields of
  `PayloadAgrees` are UNDECIDABLE.** `payload` being HALF is structural, not a gap awaiting a
  faster tactic. No WP should try to close it by `native_decide`.
- **Quotient VM cannot be unrolled** (QPROBE: stuck leaf 81,768 chars, 0 False leaves, 154 s kernel
  timeout; opcode from symbolic memory). Route B (`QInterpRefines`) is the only way.
- **Kernel cost ~3 s per unrolled 256-bit mulmod iteration; 2x fuel = 2.65x kernel; each
  `staticcall` rebuilds symbolic memory.** The old 240 ms per 13-statement block is off by ~70x on
  looping/calling blocks. Row set ~7.4 h pure kernel (n=8 targets), excluding quotient.
- **`gen_sorry.sh` is hardened (2d2c57f): refuses a shorter SORRY.md without `--allow-shrink`.**
  Never hand-edit SORRY.md. Use `scripts/lean_grep.py`, not `grep -c sorry`.
- **Six things I escalated as human blockers were already answered by the plan** (vkPins, the
  generated ordering, SIM.0, M9's irrelevance, DG.6, the proof.bin obstruction). **Check the cards,
  plan and code before declaring a blocker, and never assert git ancestry, a digest or a pin
  without running the command.**


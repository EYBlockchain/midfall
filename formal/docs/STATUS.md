# STATUS - midfall (formal/)

One page, overwritten after every merge (`v2-bundle/docs/GOAL-PROMPT.md`, D-P75). The previous
STATUS (743 lines of history, corrections and lessons) is `git show b62e29e:formal/docs/STATUS.md`;
its operational lessons now live in the goal prompt's OPERATIONAL section.

## 1. Verified at `92d5a41` (2026-11-19 16:56 UTC; from the tree and the merge reports, not a fresh verify.sh)

    root lowering_correct .... skeleton through lowering_correct_of_W; #cone_sorries 2
                               (lowering_correctW, model_quotientMode); not yet the register's root
    register ROOT column ..... the V2 fixture root lowering_equivalence_poseidon: 10 leaves,
                               1 REFUTED -> UNREACHABLE (WP A0 re-keys it to lowering_correct)
    root lowering_sound ...... not yet stated (WP A0)
    block rows ............... INTEGRATED 0 of 7 for every render (TraceReturn proved in V2's shape only)
    exhibits ................. PRESENT 2 of 4 (missing: REF.12's Lean-verifier half; WP B6)
    ValidV3 at F1 ............ NOT inhabited: clause `generated` refuted (poseidonValid_generated_not;
                               generateAll panics at quotient.rs:202); WP B4
    registered sorries ....... 77 (SORRY.md; WID.11 closed two, outside every reported root's cone)
                               · KAT 1621 checks / 117 files
    composition .............. glue rejectsV3_of_sims, completeV3_of_progs, totalV3_of_stages sorried;
                               bundles over StageBnd, rows over BlockSim: incomparable (RECON.3); WP A0

## 2. In flight

Nothing has started under the new goal prompt.

## 3. Next READY, per track

A: A0 = card PL.H0 · B: B1, B2 · C: C1 · D: none yet (D2 waits for B1, B2)

## 4. Waiting on human

1. Stop the orchestrator session still running under the old `/goal`, then paste
   `v2-bundle/docs/GOAL-PROMPT.md` (below its line) as the new `/goal`. D-P74 and D-P75 are signed
   (2026-11-19, `design.md`).
2. DG.7 (WP B1): may a WP push and delete a branch on `origin` for CI? If not, B1 runs the negative
   control locally.
3. OBJ.17 and DG.3 (WP B1) are DECISION cards: name the target fixture F1; pin the closure of the
   frozen statements.
4. Carried over, unanswered: `exitScan`'s two copies disagree on `break`/`continue` in a `for` post
   block; the `omega` flip is not refused (`PayloadAgrees`, a known limit at PLAN-V3:1123);
   `certify` is vacuous at F0; `proof.bin` is not reproducible (`OsRng` in `blind_quotient_limbs`).

## 5. Last three merges

`92d5a41` + `ccf6367` FALS2 (a cited falsifier was false, one OPEN; citations corrected) · `44d0acd`
WID.11 (register 79 → 77) · `cd736ff` QEMIT3 — none moved a PROGRESS line
(`#cone_sorries lowering_correct` = 2 throughout).
## THE ORDER IS NOW WORK PACKAGES (D-P74 + D-P75, signed 2026-11-19) - read this before the V3 table

**D-P75 amends EXECUTION-V2 sections 2-4, 7, W6, W8 and PLAN-V3 sections 7, 10.3. The order is the
COMPLETION table at the top of `QUEUE.md`; the V3 table below it is now card REFERENCE, not the
order.** Loop step 1 changes accordingly: take the first READY WP row for a free worker.

- **Unit** = one WORK PACKAGE: one outcome on the PROGRESS report, absorbing the cards in its row.
  **The absorbed cards are guidance; the WP's Accept is the contract.**
- **Box**: 8 h for `strongest`, 4 h for `Sonnet`. **WIP commit every 45 min on the WP branch.** If
  a worker's context runs out, re-brief it on the SAME WP from its last WIP commit.
- **Concurrency: AT MOST TWO WORKERS**, each in its own **long-lived WARM** worktree, on different
  tracks, or one track only if their files are disjoint. **Workers never edit `SORRY.md` or the KAT
  pins by hand.**
- **Progress is the report**: sorried leaves of each root (`lowering_correct`, `lowering_sound`,
  then `lowering_correctW`, `generator_correct`), block rows INTEGRATED (of 7), exhibits PRESENT
  (of 4), `ValidV3` inhabited at F1. **Every WP must name the line it moves. TWO CONSECUTIVE
  MERGED WPs THAT MOVE NO LINE GO TO THE HUMAN.**
- **D-P75 item 5 relief**: while `ValidV3` has no F1 inhabitant (until WP B4), W12's WITNESS for a
  statement over `ValidV3` may be the named gap `gap_lowering_correct_witness_unexhibited`.
  **The falsifier is still required and must be proved.**
- **D-P74 route**: `lowering_correct` is proved through `lowering_equivalenceV3_of_rows`, NOT
  through `lowering_correct_of_W` (which stays in the tree, unused by the root). **One row shape:
  `BlockSim`/`BlockProgS` over `StageInv`; `StageBnd`, `BlockSimV3`, `BlockProgV3` and the lemmas
  that only compare against them are DELETED.** ROOT, `#cone_report` and `verify.sh` key to
  `lowering_correct`; the V2 fixture headline is reported RETIRED until PL.H deletes it.

**WP STATE as of `548ce8b`: A0 (= PL.H0) is RUNNING in `/Users/julian/midfall-b` on `t/PL.H0`,
8 h, strongest.** **A1, A2 and A3 are all `after A0` - nothing else can start until A0 merges.**
A2 absorbs ST.13 and should resume from the preserved WIP `f71105d` on `t/ST.13` in
`/Users/julian/midfall-c` (WARM, has `.lake`) - **do not re-derive that monotonicity chain, and
do not trust its 'PROVED (ST.13)' comment: the build fails.**

**MEASURED COSTS THAT BLOW WP BOXES - plan around all of them: a COLD worktree build is ~50 min**
(Mathlib from source, no cache), **`checks.sh` is 13-35 min** and longer under contention, and
**`ram_guard --limit 6G -- lake build` is KILLED (peak 11.79 GiB) leaving `.olean` files missing,
which produces a FALSE red on the register - always plain `lake build`.** **A fresh worktree
cannot pass `checks.sh` at all until the 4 untracked F1 fixture binaries
(`proof.bin`/`calldata.bin`/`instance.be`) are copied in - `Calldata.lean:306-310` admits a fresh
clone has always been red there. Seed them at worktree creation, not after.**

---

## ST.13 - FAILED at round 142, work left on branch t/ST.13, NOT merged

**`lake build` fails on `Midfall.Yul.Bridge`** despite a diff with zero sorries and a comment claiming
'PROVED (ST.13)'. Errors: cannot synthesise implicit `alpha`/`c'` at `Bridge.lean:367`; unsolved
goals plus an unused `simp` argument at `:374`; `Unknown identifier funenvMv_cons` at `:379`. **A card's
own report that something is proved is a lead; `lake build` is the fact.**

**Salvageable, do not re-derive:** the monotonicity chain `fdeclMv`/`fscopeMv`/`funenvMv` ->
`externalCall_mono` -> `builtin_mono` -> `step_mono` -> `run_mono` -> `runCommitted_mono`, plus the design
finding that the call relation occurs only in `externalCall` (`EVMExec.lean:889`) in a positive position,
`finishCall` chooses everything the caller observes about a response, and `VEnv`/`Code`/`EvmState` do not
depend on the relation. **Resume in `/Users/julian/midfall-c` on `t/ST.13`.**

---


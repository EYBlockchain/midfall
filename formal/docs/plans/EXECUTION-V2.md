# EXECUTION-V2 — how the orchestrator runs PLAN-V2

`PLAN-V2.md` says **what** to prove. This file says **how**, for the setup in use: **one
orchestrator agent that plans and delegates one ticket at a time to one subagent**. The live queue is
`formal/docs/QUEUE.md`, the state is `formal/docs/STATUS.md`, and the main prompt is `GOAL-PROMPT.md`.

> **PLAN-V3 hand-over (added 2026-11-17; conditional on a signed D-P60 in `design.md`).** Nothing in
> this file changes before that. After it: (1) "PLAN-V2" in §2 and §5 reads "PLAN-V3"; (2) rules
> **W12–W15** (PLAN-V3 §4) are added to W1–W11: a witness and a falsifier before any brief; no
> refuted sorry kept in the tree; the model must run its object before a Yul proof card is READY;
> frozen means the meaning, and re-hashes are batched; (3) cards come from
> `docs/plans/PLAN-V3-cards.md`, entered in `QUEUE.md` by card PL.0 as one line each, and briefed
> with §3's template plus the EVIDENCE line of PLAN-V3 §7; (4) one more ticket type,
> **STATEMENT** (≤ 2.5 h): a new or changed statement lands together with its witness and its
> falsifier, and is done when its consumer compiles; (5) the progress measure of §6 is the report
> of PLAN-V3 §6 (leaf status, exhibits, block coverage, axiom sweep), with the cone count as its
> last line. The loop of §2, the subagent contract of §3 and W1–W11 are unchanged.

The design principle, from the log and from an external review of it (Appendix A): the executing
agent is good at bounded proofs, counterexamples and honest disclosure. The failures were mostly
**orchestration** failures:

- unverified premises;
- helpers proved before anyone checked they were needed;
- proxy tests;
- over-claimed milestones;
- effort spent policing unused artifacts.

So the controls sit in the orchestrator's loop, and progress is measured **mechanically, by what the
headline actually depends on**.

## 0. Roles

| who | does | never |
|---|---|---|
| **Human (H)** | owns scope and the frozen surface; answers DECISION requests; reads `STATUS.md` | — |
| **Orchestrator (O)** | picks the next ticket, checks its premises, writes a ≤ 1-page brief, delegates, **re-verifies the result itself**, merges, records | proves theorems; edits the frozen surface or scope; writes a claim a tool did not print |
| **Subagent (S)** | one ticket on branch `t/<ID>`, fresh context, WIP commits on that branch only, returns the fixed-format report | commits to `formal/baseline`; edits frozen files; pivots to a different deliverable |

## 1. Cut-over from the work in flight (once, at the next package boundary)

State at writing (verified 2026-11-16 ~17:30):

- `formal/baseline` = `15c0b3a`, the same as `origin`.
- P-DET is finished: `af46ef9` proved `dialect_deterministic` and recorded **D-P42** in `design.md`.
- **P-RUNLEG's brief is committed (`15c0b3a`) and is probably running.** It attacks D-P42 and
  reserves "D-P43" for an `ir_refines` edit.
- The register has 39 entries.

The orchestrator does T0.1–T0.4 itself, without a subagent:

- **T0.1 Drain.** Do not start another v1 package.
  - **P-RUNLEG still running:** let it return.
  - **P-RUNLEG returned green and complete:** merge it as the last v1 commit, with its claims in W7
    words.
  - **P-RUNLEG returned partial or was interrupted:** commit its tracked changes under `formal/` to
    branch `v1/p-runleg-wip`, then switch back. Never `git checkout`/restore over uncommitted work.
  - Its conclusions about D-P42 and `ir_refines` are not acted on, because D-V2 retires both. One
    piece is salvaged: the routed-calldata technique of its item 1 (`dispatcherAccepts`,
    `armPrefix_passes`, `cdWellFormed`) goes as input to the B1.0 outcome KAT ("fixture calldata
    passes the ABI guard").
- **T0.2 Freeze v1.** Tag `formal/v1-final`. Run `checks.sh` once and write the measured register
  and KAT totals into `STATUS.md`; do not copy them from a brief.
- **T0.3 Record D-V2** (PLAN-V2 §2, verbatim) as the next free D-P number (expected **D-P43**).
  - D-V2 answers the question D-P43 was reserved for: `ir_refines` is retired, not edited.
  - D-V2 is **pre-approved by the human through the `/goal` prompt**.
  - Point `PLAN.md`'s header to PLAN-V2.
  - Docs only: **do not edit any v1 `.lean` file.** `Statements.lean` is sha256-pinned, and header
    edits shift the line numbers `SORRY.md` records.
- **T0.4 Fetch the V2 bundle.** Run `git fetch origin v2/bundle && git checkout origin/v2/bundle --
  v2-bundle/`. The bundle sits outside `formal/`, where no gate scans.
  - Copy `PLAN-V2.md` and `EXECUTION-V2.md` to `formal/docs/plans/`.
  - Copy `QUEUE.md` and `STATUS.md` to `formal/docs/`.
  - Commit these docs. The Lean files are landed by Q0.1.

**What carries over unchanged.** Nothing proved is deleted, and the `checks.sh` gates keep running
untouched. V2 reuses the following directly (PLAN-V2 §8):

- `verifyNative_iff_msgs_codec`, the codec/calldata chain, `HoldsFinal.holds_exhibited`;
- `traceReturn_spec` (its cone is sorry-free, measured), the QVM partial results
  (QVMARMS/READOFF/CONTSLOT), Bridge, Inv, Snapshot.

**What stops.** Every v1-only thread stops:

- `ir_refines`, `RunShell`, ShellModel as a target, M8, P-RUNLEG items 2–3;
- the `LoweringCorrect` fields and the `Partials` specs over `Surface`;
- gate work, accumulator mode, S1–S7.

Old briefs stay in `docs/plans/` as history; `QUEUE.md` is the only live queue. The 39 register
entries are mapped in `QUEUE.md`: 17 reuse candidates, 14 retired with v1, 8 parked.

**The retired dependency is removed in the build, not just in the queue.**

- **The leak.** The provided V2 files still reach retired modules: `Statements.lean` imports
  `Surface`, `Partials` and `Accumulator`, and `Program.lean` reaches them via `FrameWalk →
  RunEmitted`. This was measured: those imports are the only route.
- **The fix.** Q0.2 copies the seven small definitions and the `freeNames` walker that V2 uses, then
  drops those imports.
- **The guard.** `ConeReport` asserts `#imports_avoid` and `#cone_avoids` for 14 retired or parked
  modules. From then on, reintroducing a retired dependency is a **build error**, not a judgment
  call.

## 2. The orchestrator loop (one iteration per ticket)

1. **Load state.** Read `STATUS.md` and `QUEUE.md`, not ETA/REVIEW/design/PLAN in full.
2. **Pick** the first READY ticket in `QUEUE.md` order. It is READY when its dependencies are
   merged, and its `advances` node is in the current cone report, or the ticket is a SKELETON that
   creates such nodes (W3). If nothing is READY, draft the pending DECISION or stop and tell the
   human.
3. **Check premises at the current commit**, ≤ 10 min.
   - A "verified fact" is a command output or kernel-checked theorem from *this* commit: `#check`,
     `#print axioms`, `#cone_sorries`, `#eval`, `rg -n`.
   - Comments, docstrings, ETA/REVIEW prose and earlier reports, including your own, are **leads**:
     they go under "verify first".
   - Run the card's **NEEDS snippet** (§3) with `lake env lean` under `ram_guard.sh`. A line that
     fails to elaborate is a false premise: fix the card, do not brief it.
   - If checking a premise would take longer, issue a PROBE ticket instead.
4. **Brief and delegate.** Use the §3 template, ≤ 1 page; one subagent, one ticket.
5. **Re-verify on `t/<ID>`**, without trusting the report. The subagent ran only
   `verify.sh --quick`. **You run the full `verify.sh` exactly once per ticket**, and never a second
   full KAT pass.
   - The full `formal/scripts/verify.sh` is green.
   - `#print axioms` and `#cone_sorries` of each delivered theorem and of the root;
   - `git diff --stat formal/baseline...t/<ID>`: no frozen file touched, no unexpected deletion, no
     file shrank unexpectedly;
   - the **consumer check** (PROOF tickets): the delivered lemma replaced a `sorry` in its consumer,
     and the root's cone count went down;
   - the **outcome check** (KAT and exhibit tickets): the intended outcome was reached at the
     intended place (§4).
6. **Classify and merge.**

   | outcome | action |
   |---|---|
   | DONE | squash-merge into `formal/baseline` |
   | PARTIAL (green, WIP lemmas sorry-registered) | squash-merge |
   | NEGATIVE (premise false or statement refuted) | merge only the evidence (the counterexample theorem); restate nothing |
   | FAILED | merge nothing; keep the branch |

7. **Record.**
   - **Commit message:** the report, with claims rewritten from what step 5 printed (W7).
   - **ETA:** one row (§6).
   - **`STATUS.md`:** overwrite with the cone count, root axioms, last outcome and the next 3 READY
     tickets.
   - **`QUEUE.md`:** state change; children from SKELETON/PROBE reports; blockers *with* reproducers.
8. **Triggers (§6).** If a DECISION is needed: write a ≤ 1-page request under "Waiting on human" in
   `STATUS.md`, mark its dependants BLOCKED, and continue with other READY tickets. A decision exists
   only once the human has signed it off (W2); until then it is PROPOSED and nothing is built on it.
9. **Context hygiene.** Every ~10 tickets, or when the orchestrator's context is past ~60%, end the
   session. A fresh one resumes from `STATUS.md` + `QUEUE.md` + this file + the goal prompt. If that
   is not enough, fix `STATUS.md`.

Orchestrator budget per ticket: about 20 min plus the `verify.sh` run. The log's turnaround from
feat commit to the next brief was 0–7 min (median 1), i.e. no checking step at all.

## 3. Subagent contract

Brief (≤ 1 page; the orchestrator copies the card from `QUEUE.md` and adds the commit and the
evidence):

```
TICKET <ID> · <layer: INFRA|GEN|ALG|SEM> · <type> · box <h> · branch t/<ID> from <commit>
GOAL: <one sentence>                                  CONSUMER: <theorem that will use the result>
NEEDS (verified at <commit>): <exact names, file:line — evidence (command → output)>
DOES NOT NEED (do not open, do not investigate): <the tempting wrong prerequisites, by name>
VERIFY FIRST (≤20 min; stop if false): <claims taken from comments, prose or earlier reports>
NEEDS SNIPPET (run by the orchestrator at <commit> before briefing, output pasted): one `#check` /
        `#print axioms` / `#eval` line per name in NEEDS; any failure means the card is fixed first
DO: <≤ 5 steps>
DELIVERABLE: <exact Lean names and signatures; nothing else>
ACCEPTANCE: <commands + expected output; for KAT/exhibit: the intended outcome and where it occurs>
DO NOT: edit frozen (sha256-pinned) files, v1 files or vendor/; add gates, scripts or docs; restate
        statements; run checks.sh or a full KAT pass (KAT tickets: one kat_gate run at the end)
STOP AND REPORT IF: a premise is false · something outside NEEDS seems required (PREMISE GAP: give
        the exact goal state that needs it; do not investigate it) · a frozen statement looks false
        or vacuous · <1/3 done at 1 h · any single tactic/computation exceeds 60 s · RAM guard trips
```

Report (≤ 15 lines; fixed fields so the orchestrator can check each one):

```
OUTCOME: DONE | PARTIAL | NEGATIVE | FAILED
DELIVERED: <names> — proved | stated | exhibited | conditional on <X: open | inhabited | refuted>
CONE: <root> <before> → <after>      AXIOMS: <#print axioms per delivered theorem>
VERIFY: verify.sh --quick green | red (<first failing line>)
PREMISES THAT FAILED: <brief claim — evidence>
BLOCKER: <minimal reproducer: example + error text, at commit>  | none
MEASURED: <hours, Lean lines; proof tickets: Yul statements covered>
LIMITS: <what the result does not cover>
NEXT: <child tickets, each with its size and the evidence for it>
```

## 4. Ticket types and acceptance

| type | box | done when |
|---|---|---|
| PROBE | ≤ 1 h | the report has the measured values and the commands that produced them |
| SKELETON | ≤ 2 h | the consumer compiles from named, `sorry`'d sub-lemmas; each sub-lemma is probed (an `#eval` on deployed data, or differential enumeration as in REVIEW R-70) and sized; children are in `QUEUE.md`. The cone count may **rise**: that is the point. The **glue** (sequencing, transport and composition lemmas) is proved, not `sorry`'d: only leaf obligations (one per block or per clause) may be `sorry`. A sorried glue lemma hides the next ceiling (C.2 → S.1) |
| PROOF | ≤ 2.5 h | the node is proved and **used by its consumer**. The card states in advance whether the root's cone falls: it can fall only when the consumer is in the root's cone and this node was its last open input. An accept line that cannot be met by construction is a defect in the card, fixed before briefing (T.2) |
| EMIT | ≤ 2.5 h | one `GenAst` region; its token KAT equals the ported codegen's text; a one-literal mutation reddens |
| PORT | ≤ 2.5 h | one Rust fn under port rules R1–R11 (`docs/PLAN.md:143`); golden KAT green at the deployed value |
| KAT | ≤ 1 h | one decidable fact at the deployment, with its **intended outcome** (below) |
| DECISION | ≤ 1 page | the human answered; the orchestrator continued meanwhile |

- **Consumer first.** A lemma that no compiled consumer uses is not a ticket. "Prove the helpers,
  then see if they suffice" was the QVM chain's failure: three passes, each finding another missing
  requirement.
- **Family rule** (opcodes, gates, MSM terms, helpers: anything with many similar cases). The
  SKELETON delivers two things:
  - (a) **one shared case-split lemma**, whose hypotheses are the per-case facts;
  - (b) **the complete per-case requirements table**, computed by `#eval` on the deployed object.

  PROOF tickets then fill table rows. Setup and case analysis are written once; nothing is discovered
  one pass at a time. Existing lemmas (for example QVMARMS/READOFF/CONTSLOT) fill cells; they do not
  start new passes.
- **Outcome-level acceptance.** An exhibit or KAT names the intended outcome and where it occurs. For
  example: "the fixture proof's calldata runs the program to `return(abiTrue)`", or "flipping one
  proof byte reverts in TranscriptParser".
  - A run that stops at an earlier guard (VK mismatch, ABI bounds, decoder failure) **fails** any
    end-to-end or readiness claim.
  - Fixtures must be **coherent**: VK, plan/layout and calldata come from one fixture set
    (`formal/fixtures/conformance/poseidon/`), are turned into pure terms by D.1/D.2, and pass the
    **coherent success-path check D.3** (layout, meta, decode, transcript, negative control) before
    any ticket uses the deployment. They are never typed in.

## 5. Rules

PLAN-V2 §4 (content rules 1–12) still applies. The tag says who each rule binds.

- **W1 Scope [O].** The cone decides. A ticket advances a node in the cone of the current root, or
  creates such nodes (SKELETON). Out of scope until the headline is proved:
  - accumulator mode, the external evaluator, embedded VK;
  - anything solc (`ir_refines`, `RunShell`, M8);
  - S1–S7;
  - curve-model work beyond `HypothesesInhabited`.
- **W2 Statements [O+S].** A new or changed statement gets its own ticket, with two pieces of
  evidence kept next to it: a witness that **all** its hypotheses hold together at the deployment,
  and a falsifier. No registry. The frozen surface changes only by human DECISION; there are no
  orchestrator decisions on delegated authority. A DECISION counts only when `design.md` quotes the
  human's sign-off: who, when, and where (message, commit or PR). An entry without one is PROPOSED:
  it changes nothing, and no ticket may depend on it. Evidence cited for a decision is landed (a
  theorem at a commit), not a scratch run.
- **W3 Consumer first [O].** Skeleton the consumer before proving its parts. Families get one shared
  case-split lemma and a complete requirements table first (§4).
- **W4 Time box [S].** One deliverable, ≤ 2.5 h. At 1 h with less than a third done: commit WIP to
  `t/<ID>`, report PARTIAL, stop. The orchestrator splits.
- **W5 Evidence [O+S].** Facts are command outputs or kernel-checked theorems at the current commit.
  Prose and earlier diagnoses are leads. A **blocker** is a minimal reproducer (an `example` plus the
  error text, at a commit), never a sentence; it is re-run before any brief relies on it. Sizes are
  measured, never asserted. A reproducer or probe result that a card or decision relies on is landed
  (in the tree or in the merged evidence), never left in `/tmp`: R-72's reproducer and S.1's
  restatements were both lost that way.
- **W6 No policing, no bookkeeping [O+S].**
  - No new gates, registries or ledgers.
  - No demonstrations that unused theorems can be deleted; no gate or KAT counts reported as progress.
  - The existing `checks.sh` suite runs unchanged. The only new tooling is the cone report (Q0.2)
    and `verify.sh` (Q0.3).
  - **Subagents write no docs**: their report is the only prose they produce.
  - **Handoffs.** Text the orchestrator copies from one report into another card is ≤ 10 lines of
    names, signatures and command output. Prose predictions in handoffs caused T.2's false premises.
  - The orchestrator writes exactly four things per ticket: the commit message, one `STATUS.md`
    overwrite, one ETA row, and the `QUEUE.md` line updates. There are no overlapping progress
    reports.
- **W7 Claims [O].** Claims are generated from tool output.
  - *Proved* means clean `#print axioms` **and** used in the cone.
  - *Conditional on X* always states X's status: open, inhabited or refuted.
  - *Exhibited* means the intended outcome on coherent fixtures.
  - "Headline proved" is reserved for `lowering_equivalence_poseidon` with `#cone_sorries` = 0 and
    clean axioms.
  - Commit subjects never say PROVED for a conditional, and a proxy run is never called end-to-end.
- **W8 Docs [O].**
  - `STATUS.md` (≤ 1 page) is overwritten each ticket: first the ConeReport and `#print axioms`
    output of the last full `verify.sh`, verbatim, then ≤ 10 lines of prose. Nothing from an earlier
    ticket survives unless it is still true. `QUEUE.md` has one line per ticket.
  - The report is the commit body; `ETA.md` gets one row per ticket.
  - `REVIEW.md` only for real defects; `design.md` only for human decisions.
  - New docstrings ≤ 5 lines. `PROGRESS.md` is retired.
- **W9 Operational safety [S+O].**
  - **Edits.**
    - Work on branch `t/<ID>`. Make a WIP commit at least every 45 min and before any risky step.
    - Never run `git checkout -- <file>`, `git restore`, `git reset --hard` or `git stash drop` on
      uncommitted work. To discard something, commit it to the branch first.
    - Never round-trip a file over 1,500 lines through a read/write tool. After a scripted edit,
      check `git diff --numstat`.
  - **Computation.**
    - A single tactic call or evaluation gets at most 60 s. Try it first on the smallest slice, in a
      scratch file, with `perl -e 'alarm shift; exec @ARGV' 60 lean scratch.lean` under
      `ram_guard.sh --proc-limit 6G`.
    - If it is over the limit, restructure: per-block or per-function lemmas, `native_decide` in
      `Instances/` for deployment facts, or fuel per nesting level. **Never retry the same computation
      unchanged.** Never `rfl` or `decide` over a whole generated program, and never raise
      heartbeats.
  - **Verification passes.**
    - The subagent runs `verify.sh --quick` and never `checks.sh` or a full KAT pass. Exception: a
      KAT ticket may run `kat_gate.py` once, at the end.
    - The orchestrator runs the full `verify.sh` once per ticket.
    - One build at a time.
- **W10 Model routing [O].** If the harness lets the orchestrator pick the subagent model: the
  strongest model for SKELETON, T, C.2/C.3 and PROOF tickets in TranscriptParser, Quotient and PCS;
  Sonnet for the rest. Otherwise keep SKELETON tickets small.
- **W11 Layers [O+S].** Every ticket has exactly one layer:
  - INFRA: landing, tooling;
  - GEN: facts about the generator or deployment, decided by computation;
  - ALG: Lean mathematics on the verifier side, with no Yul (for example the pairing-check algebra
    under `Holds`);
  - SEM: Yul semantics of the program.

  A ticket's NEEDS lie in its own layer or in already-proved lemmas of another. It never
  investigates another layer's machinery. In particular, the pairing **product is a parameter**: no
  ticket implements a pairing. If something outside NEEDS seems required, that is a PREMISE GAP: stop
  and report the exact goal state.

## 6. Progress, claims, estimates

- **Progress measure.** `#cone_sorries <root>` lists the sorried declarations the root depends on.
  The tool is `tools/ConeSorries.lean` in the bundle, which also provides `#cone_in`, `#cone_avoids`
  and `#imports_avoid`.
  - It passes 8 self-tests on v4.35.0. On this repo's build, `traceReturn_spec` gives 0 and
    `transcriptParser_spec` gives 1 (itself), in about 30 s including loading.
  - It also produced Q0.2's exact move list.
  - Roots: `lowering_equivalence_of_blocks` and `end_to_end` until C.1, then
    `lowering_equivalence_poseidon` (plus `end_to_end` at the deployment).
  - `verify.sh` prints the count; `STATUS.md` carries it.
  - Register totals, gate counts and KAT counts are **not** progress measures.
- **Cone status.** `STATUS.md` marks every sorry in the root's cone OPEN, REFUTED (a proved negation
  exists, e.g. `poseidonRender_notValid`) or BLOCKED (waiting on a decision or on data). A REFUTED
  node means the root is unreachable by the current route: the next ticket addresses it (fix the
  object, or re-plan with the human), and tickets whose only effect is downstream of it are not READY.
- **ETA row per ticket:** ID, type, box, actual h, cone before→after, premises held (y/n), outcome.
  No derived percentages.
- **Calibration, not extrapolation.** No schedule beyond PLAN-V2 §9's prior until **calibration
  point 1 (C.5, the first composed slice)**.
  - At each point, record the tickets and hours since the previous point, cone nodes closed, and
    block contracts integrated.
  - Re-estimate the remaining cone by analogy, stating the sample size.
  - Points: C.5; end of TranscriptParser; after the QVM interpreter refinement.
- **Stop and re-plan** if 3 of any 5 consecutive tickets miss their deliverable, or 2 of 5 had a
  false premise. Re-planning is reorder/split in `QUEUE.md`; scope or frozen-surface changes go to
  the human. While the trigger holds, start no PROOF or SKELETON ticket: write the re-plan under
  "Waiting on human" and run only PROBE and KAT tickets until the human answers.

## 7. Queue

`QUEUE.md` is the live, ordered queue of **ticket cards**. Every card has the same fields: layer,
type, box, model, goal, NEEDS with file:line, DOES NOT NEED, VERIFY FIRST, ≤ 5 steps, deliverable,
accept, stop-if. With one subagent it is a single priority list:

1. **CUT-OVER and Q0.** Drain v1; land V2; cut the retired imports and guard them; freeze; review.
2. **CORE**, consumer-first to the first calibrated slice:
   - the deployment's inputs as pure terms (D.1, D.2);
   - **the coherent success path (D.3), before anything uses the deployment**;
   - the headline skeleton at the deployment (C.1), which fixes the cone, then frames (M0.1),
     composition (C.2) and validity (C.4);
   - the FinalPairing skeleton (FP.0), with its algebra (P.1, ALG) kept separate from its semantics;
   - automation (T.1–T.5), with every tactic accepted only by closing a named node;
   - the first composed slice (C.5); the rejection skeleton (C.3).
3. **GEN.** Codegen agreement, emitters and port inventories for the clause nodes C.4 names. Run GEN
   when CORE is blocked, and after calibration point 1.

Later epics each start with a SKELETON ticket that writes cards for its children in the same format.
Families follow the family rule (§4).

---

## Appendix A — why: the log (Nov 12 21:45 → Nov 16 14:56) and an external review

**Measured.** In that window there were 44 packages, 88 h, counted from plan commit to feat commit;
those windows also contain the orchestrator's own time.

- The solc/M8 track was 7 packages and 18.3 h. 12.5 h of that was started after your scope
  correction (`d0dd244`, Nov 15 12:13).
- The track continued after the window: P-DET (99 min, `af46ef9`), then P-RUNLEG.
- The register grew 14 → 64 in 12 h on Oct 27–28, when the v1 statements were written in bulk.
- The orchestrator's ledger records 8 false premises in its own briefs in one session. Its own
  stated pattern was "I assert a blocker's size or a rule's coverage without deriving it" (ETA:808).
  18 recorded blockers turned out to be tactic failures (ETA:495).

**Judgment, not measurement.** I sorted packages by how much V2 can reuse them. Roughly a sixth is
reused as is, roughly a third is partly reusable, and roughly half is off the V2 path or discarded.
Others could draw these lines differently; the figures motivate the rules but are not productivity
metrics.

**Where the avoidable time went (review feedback), and the concrete change for each:**

| # | avoidable time | change | where |
|---|---|---|---|
| 1 | **Wrong prerequisites investigated.** An algebraic pairing-check lemma was treated as needing execution semantics; a pairing implementation was assumed necessary when the product is a parameter | Every card has one layer (W11) and explicit NEEDS / DOES NOT NEED lists. The headline quantifies over `product`. The algebra (P.1, ALG) is separate from the semantics (T.4/T.5). Anything outside NEEDS is a PREMISE GAP, reported and not investigated | W11, §3, QUEUE C.1/FP.0/P.1 |
| 2 | **IR/shell-model detours** after the source-only scope decision; the impossible obligation kept driving work | D-V2 retires it. Q0.2 removes the measured import chain and the copied definitions. `#imports_avoid` and `#cone_avoids` make re-entry a build error | §1, QUEUE Q0.2 |
| 3 | **Repeated QVM passes** (instruction lengths, then read bounds, then constant slots, each finding more) | Family rule: one shared case-split lemma plus a complete requirements table computed up front. Existing lemmas fill cells | §4, W3, QUEUE B4.0 |
| 4 | **Inadequate fixtures.** A deployment fixture could not decode, then a key/layout mismatch surfaced | D.1–D.2 build pure terms from one fixture set. D.3 runs the coherent success-path check (layout, meta, decode, transcript, negative control) **before** any ticket uses the deployment | §4, QUEUE D.1–D.3 |
| 5 | **Over-scoped assignments and bookkeeping.** The four-item codec brief; gate hardening; deletion experiments; overlapping reports | One deliverable per card; a ≤ 2.5 h box with a 1 h checkpoint. No gates, no deletion demos. Subagents write no docs; the orchestrator writes exactly four things per ticket | W4, W6 |
| 6 | **Unproductive computation and lost edits.** An 18-min failed reduction; an 18-min / 8.7 GiB generated-code reduction; uncommitted proof edits reverted; duplicate full KAT passes | 60 s limit per tactic or evaluation, smallest slice first, restructure rather than retry. WIP commits on `t/<ID>` and the destructive git commands banned. Subagent runs `--quick` only; one full verify per ticket, by the orchestrator | W9, §2.5 |

| shortcoming (log; external review) | change in this plan |
|---|---|
| Dependency analysis wrong: comments and earlier diagnoses taken as facts; blockers that were irrelevant, already resolved, or tactic problems | Mechanical dependencies via the cone report; evidence rule W5; blockers are reproducers |
| Milestone reporting unreliable: "headline proved" for a conditional whose certificate was missing | W7 claims generated from tool output; "headline" reserved for an empty cone |
| Proxies tested instead of outcomes: undecodable fixture, incoherent key/layout, run ending at VK mismatch | §4 outcome-level acceptance; pure terms from one fixture set and the coherent success path (D.1–D.3) |
| Helpers proved before sufficiency was checked (QVM passes) | W3 consumer first; PROOF is DONE only when used by its consumer |
| Effort spent policing unused artifacts (gate counts, deletion demonstrations) | W6; the falsifier registry I first proposed is dropped |
| Operational losses: expensive unfolding, resource use, lost edits/restores | W9: ticket branches, WIP commits, no restores, profiling |
| Over-scoped briefs (P-CODEC); unbounded passes | W4 box; one deliverable per ticket |
| Scope correction not honoured; orchestrator decisions on frozen statements (D-P39–41) | W1 cone-scoped tickets; D-V2 pre-approved; frozen surface sha256-pinned, human-only |
| Overconfident estimates; the review also cautions about my own percentages and token extrapolations | No forecast beyond a labelled prior; calibration points; no derived percentages in ETA |

**Keep** (both the log and the review agree these worked):

- bounded lemma proving;
- counterexample discovery, now reported as NEGATIVE outcomes;
- differential testing before induction (R-70);
- narrow, ordered packages (the CODEC-A/B/C split succeeded where P-CODEC failed);
- detailed disclosure of limits, now the `LIMITS` field of the report.

The agent and its proofs are retained. What changes is how tasks are chosen, briefed and accepted.

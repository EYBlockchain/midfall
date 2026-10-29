# Work package plans

Detailed handover briefs for implementing agents. One file per package: `P-NN-<slug>.md`.

A plan file is written by the orchestrator (planner) and consumed by exactly one
implementation agent. Plans are refined incrementally as the port advances - a plan that
was written before its dependencies landed is a guess, so the sections marked
`TO CONFIRM` must be resolved against the actual tree before the package is fired.

## Conventions

- **Status:** `READY` (fire now), `BLOCKED` (naming the blocker), `DRAFT` (hazards not
  yet verified against source), `DONE` (committed, with the commit hash).
- Every plan names its Rust file(s) with line counts **at HEAD**, the Lean file(s) it
  creates, the packages it depends on, and the packages it unblocks.
- Hazards are numbered and each one must be answered in the agent's report. A hazard is
  only allowed in a plan if the planner actually looked at the source and found it.
## Queue

See PLAN 14.7 for dependency order and **PLAN 14.8 for the M3 scope cut**. Board:

| pkg | plan | status |
|---|---|---|
| P-05..P-09d | abi, encoding, api, kzg, vk, memory, vm types/interp/builder/certify | DONE |
| P-09e | [validator](P-09e-validator.md) | in flight |
| P-09f | shape recognizers (vm/mod.rs 3156-3227, 3649-3813) | DRAFT |
| P-09h | `yul_emit.rs` | DRAFT |
| P-10 | `quotient.rs` + `direct/folds.rs` | DRAFT |
| P-11 | `plan` + `config` + `mod` | DRAFT - needed for `L.plan.qprog` and `Supported` |
| P-12 | `calldata` + `builder/*` + `evm` | DRAFT |
| P-13 | [templates](P-13-templates.md) | DRAFT - widest error bar |
| P-SE | [semantic-equivalence statements](P-SE-semantic-equivalence.md) | APPROVED - full statement surface + proof plan; evidence in P-SE-evidence/ |
| ~~P-14~~ | ~~listing, disasm, diagnostics~~ | **CUT** (PLAN 14.8) |
| ~~P-09g~~ | ~~direct/{mod,emit,layout,validate}~~ | **DEFERRED to M10** |

| pkg | plan | status |
|---|---|---|
| P-05 | abi + encoding | in flight |
| P-06 | [P-06-api.md](P-06-api.md) | READY |
**Both AST relations are necessary but NOT sufficient against zero-valued profile data.** P-AST3b measured that hard-coding four accumulator words to 0 reddened neither `yulTokens` nor `stmtsBeq`, because the deployed profile values ARE 0 - only a plan-dependence gate (perturb the plan, require the output to move) caught it. Any slice whose deployed values are zero, empty or degenerate needs a plan-dependence gate alongside the two relations.
- **Two file-corruption traps that cost a cycle each.** (1) A Lean doc comment written `/-! ---- text ---- -/` does NOT close - the dash run right after `/-!` makes the whole rest of the file an unterminated comment, reported only at EOF. Use `/-` or put a space after `/-!`. (2) Neither `yulTokens` nor `stmtsBeq` can distinguish hex from decimal literals: a constructor-built `320` and a `yul%` `0x0140` are equal under BOTH relations, so numeric notation cannot be pinned by any AST relation and needs a string-containment gate.
- **Non-vacuity obligation (D-P23, standing).** Every stated theorem or structure field needs BOTH a satisfiability witness for its hypotheses AND a perturbation that breaks its conclusion. No witness means vacuous; no breaking perturbation means decorative - defer it with a blocker instead of shipping it. Text-fragment gates do not satisfy this. Statement-only adversarial reviews repeat after every batch lands, including after repairs.
- **Proof statements come from the sketches, not from summaries.** For any P-SE stage the normative Lean statements are `P-SE-semantic-equivalence.md` sections A-R; see `P-SE-statements.md` for the section-to-line-range map and the list of sketched identifiers that do not resolve. A brief citing only the index entries is under-specified.
- | P-07 | kzg | DRAFT |
- **Never perturb the working tree in place.** Apply R-41 source mutations to a copy outside the repo, or verify with `git diff --numstat` after every harness run. A killed D6 harness left `.reverse` deleted from `MultiPrepare.fEval` - a semantic change that built clean and passed KATs (R-54).
| P-08 | vk | DRAFT |
| P-08 | vk | DRAFT |
| P-09 | quotient_numerator vm + direct | BLOCKED on P-06, P-07 |- **`List.range' start n` takes a COUNT, not an inclusive end.** `List.range' 0 3 = [0,1,2]`
  and `List.range' 5 3 = [5,6,7]`, so `List.range' a (b - a)` is exactly Rust's `a..b`.
  A P-09h report claimed `FoldTypes.lean:504` mis-ported `lp.start..lp.end` on the
  grounds that `range'` is inclusive, and stated a verification (`range' 0 3 = [0,1,2,3]`)
  that does not reproduce - the orchestrator measured `[0,1,2]`. **The port was correct
  and was not changed.** Applying the proposed "fix" would have introduced an off-by-one
  into working code. Lesson, aimed at both author and reviewer: a claimed defect in
  inherited code needs the measurement re-run by whoever acts on it, especially when the
  remedy is to edit a file the finder does not own.
- **`List.zipIdx xs` yields `(element, index)`**, the reverse of Rust's `.enumerate()`
  which yields `(index, element)`. Verified: `zipIdx [10,20,30] = [(10,0),(20,1),(30,2)]`.
  Every `a..b.map(|(i, x)| ...)` port has to swap. This part of the same P-09h report was
  correct and cost seven sites in that file alone.


## Standing notes for agents (each cost someone an hour)

- **`lake env lean FILE` does not apply lakefile options** such as
  `autoImplicit = false`. It accepts code `lake build` rejects. Two agents have been
  bitten. Every number you report must come from `lake build` and
  `scripts/checks.sh`.
- **Lean is order-sensitive.** Types must be declared before use, so a Rust item order
  that reads naturally top-to-bottom may need moving; when you move one, say so at the
  site (Encoding.lean moved `LookupEvalSlots` below `Word` and recorded it).
- **Some Rust identifiers are Lean reserved words.** `meta` cannot even be a `let`
  binder in Lean 4.35; the convention is a trailing underscore (`meta_`, `instance_`).
  Record every such deviation - it is an R2 exception and a reviewer will look.
- **`Vec` -> `List` in the Generator row**, despite PLAN R6 literally saying `Array`.
  The divergence is recorded in PLAN 14.7 and Protocol.lean's header; follow the row.
- **Do not edit a file another package owns** to fix something you noticed. Report it as
  a finding (F5: `Location`/`Value`/`Ptr` carry no `BEq`; F8: two const blocks landed in
  Abi.lean that belong in Layout.lean). Both are queued below.

## Cross-package work owed (not any single agent's task)

| item | source | why |
| `vm/disasm.rs:41-50` hand-copies VM_LIMBS, PAIRWISE_COEFFS, LIMB_STRIDE and both MODARITH7 flags as literals; nothing ties them to the constants (P-09a F-2) | P-09g | a limb-count change silently desyncs the disassembler |
| `QuotientExecutionKind` and `QuotientIdentityExecution` are isomorphic enums cargo cannot tell apart (P-09a F-3) | P-09b | gate 28 ties them in Lean only |
| `Vk.lean:379-387` says its `VkQuotientBuild` projection should become an alias once the full record lands - it has (P-09a F-4) | P-09b | stale note, and a projection that should be an alias |
| Retire the `VkBuildEnv` shim: five precise edits listed in the P-03e report, including a gate that only passes because the stub copies config fields into unrelated ones | next Vk touch | `memoryLayoutFor_config_ok` is currently testing the stub, not the real constructor |
| Upgrade `YulGolden.lean`'s nine pasted pins to reading the dump directly (D-P19) | after M3 | retires a drift class the provenance script polices by hand |

Also from D-P19, as a standing rule: **gates should read the artifact at `#eval` time**
rather than comparing a pasted string, and a KAT section that reads files must put its
reachability gate first so a wrong path is diagnosed rather than silently matched.

|---|---|---|
| Add `deriving BEq` to `Location`, `Value`, `Ptr` in Filters.lean / Models.lean | P-05 F5 | every later package that tests a pointer re-invents a comparator |
| Move the LM:365-377 and LM:379-393 const blocks from Abi.lean to Layout.lean | P-05 F8 | they are the Layout row's content; the move is mechanical because gates cite by name |
| Add `memoryguard` and `setimmutable` to the vendored EVM dialect | D-P15 | prerequisite for M8's IR import; `Op` is a closed enum so it cannot be done from Midfall/Yul |
| Re-run the full `scripts/gate_negctl.py` including its kat half | R-41 | the kat half was run ad-hoc, not as the committed script |
| Decide the `Vec`/`Array` question in PLAN R6 | P-04 F5 | two conventions split along a phase boundary |


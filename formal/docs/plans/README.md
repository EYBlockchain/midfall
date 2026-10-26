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
- Acceptance always includes: `lake build` green, `bash scripts/checks.sh` green, a
  per-gate perturbation actually run (PLAN 12, R-41's rule), and non-vacuity evidence.
- Plans do not repeat PLAN section 4's R1-R11 rules; they point at them and record only
  the file-specific application.

## Queue

See PLAN 14.7 for the dependency-correct order. Current board:

| pkg | plan | status |
|---|---|---|
| P-05 | abi + encoding | in flight |
| P-06 | [P-06-api.md](P-06-api.md) | READY |
| P-07 | kzg | DRAFT |
| P-08 | vk | DRAFT |
| P-08 | vk | DRAFT |
| P-09 | quotient_numerator vm + direct | BLOCKED on P-06, P-07 |

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


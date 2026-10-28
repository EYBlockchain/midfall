# P-IR - `ImportSolcIR`: the last prerequisite for a stated `ir_refines`

Status: READY. P-VEND (`9fe74f9`) removed the dialect blocker; the deployed runtime object
already elaborates as a `yulObject%` quotation with **no `sorryAx`**. What is missing is
that **no imported object exists in the tree** - D-P15's script was never written.

## Deliverable

`Midfall/Yul/ImportSolcIR.lean`, **generated** from the pinned solc `ir` artifact of the
tracked deployed sources, per D-P15: textual via-ir IR, imported as `yul%` quotations,
with the elaborator as the checker. Plus the generator script that produces it, so the
import is reproducible rather than a one-off paste.

## Two decisions to make explicitly, not by accident

1. **`ir` vs `irOptimized`.** P-VEND measured that `memoryguard` survives both, with a
   different *argument*: `ir` says `memoryguard(128)`, `irOptimized` says
   `memoryguard(0x08e0)`, and the **deployed bytecode begins `PUSH2 0x08e0 PUSH1 0x40
   MSTORE`** - exactly what `Generator/Evm.lean:129` reads back.
   **Orchestrator's ruling: pin `ir`.** PLAN section 7 says `irCheck` validates *the
   unoptimised IR*, and the Yul-optimizer hop is explicitly in the trusted base - covered
   by differential testing, not proved. So the 0x80-vs-0x8e0 divergence is a **stated
   consequence of the trusted hop**, not a defect. Record it in the file header and in
   `docs/design.md` so nobody later reads it as an oversight.
2. **The two alpha-renames.** P-VEND measured 4,547 `$` characters in identifiers (the
   generator's `usr$` prefix and solc's `abi_decode_t_array$_t_uint256_$dyn_…` mangling)
   and 6 uses of the bare identifier `end`. Lean's ident lexeme rejects `$`; `end` is
   reserved. **Choose one and justify it:** rename at emit time (deterministic, reversible,
   keeps the DSL untouched) or extend the DSL lexer. Recommendation: **rename at emit
   time**, with the mapping recorded in the generated file's header so the correspondence
   to the artifact is auditable, and a gate asserting the rename is injective and that no
   original name survives.

## Hazards

1. **The import must be reproducible.** A committed 2,610-line generated file that nothing
   can regenerate is a paste, not an import. The script, the solc version/sha256, and the
   exact `--standard-json` settings go in the repo, and a gate should re-derive at least a
   digest of the artifact at `#eval` time (D-P19).
2. **Do not weaken what is imported.** If some construct will not elaborate, report it
   precisely rather than deleting the offending statements. A partial import presented as
   complete is the vacuity class again.
3. **`RunContractIR` needs a witness.** P-VEND's obstacle (3): the only `Surface` in the
   tree is the confined fixture, and D-P17 keeps `Instances/` out of theorem-bearing
   files. So an explicit `exists obs, RunContractIR ...` witness lives in `Instances/`.
   That is fine - say which file and why.
4. **Verify existence with `#check`, not grep.** The orchestrator's own truncated grep
   produced a false `stmtsBeq` defect claim that reached the human as a blocking decision.
5. **Never perturb the working tree in place** (R-54). Use copies, or verify
   `git diff --numstat` after every batch.
6. Register the module (R-50). Numbers from `lake build` and `scripts/checks.sh` only.

## Rules

Do NOT edit Rust files, `Statements.lean`, or `vendor/` (P-VEND's authorisation was for
that package only). Do NOT git add or commit. Doc comments in the style of
`Exec/Accumulator.lean`. **R-41** binds: perturbations actually run, failures reported.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 1124 across 72 files.
- The generated import elaborates, with `#print axioms` on the resulting object free of
  `sorryAx`.
- **Required finding**: state whether `ir_refines` and `lowering_equivalence` can now be
  STATED with a real (non-uninhabited) `RunContractIR` hypothesis, and name anything still
  missing. That is the gate on stage 6's headline.

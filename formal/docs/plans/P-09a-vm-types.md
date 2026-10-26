# P-09a - the quotient VM vocabulary (types and opcodes from vm/mod.rs)

Status: BLOCKED on P-03e (memory layout) only loosely - it needs `WORD_BYTES` and the
layout constants, which are already ported, so this can actually run in parallel with
P-03e if the queue allows. It blocks P-09b (`QVM.run`), which blocks M6.

Reference: `proofs/solidity-verifier/src/lowering/quotient_numerator/vm/mod.rs`
(4,336 lines at HEAD). **This package takes only the vocabulary**, roughly KZ:85-550 plus
the type definitions at `:548-572` (31 `Q_OP_*` opcode constants), `:953`
(`QuotientExpr`), `:1038` (`QuotientMem`), and the record types
(`QuotientTarget`, `QuotientIdentity`, `QuotientIdentityMetadata`, `QuotientProgramItem`,
`QuotientProgramPlan`, `QuotientProgramBuild`, `RepackedProofLayoutPlan`,
`RepackedProofScalarLayout`, `SelectorFoldPlan`, `QuotientExecutionKind`,
`QuotientLimbShape`, `QuotientLeaf`, `QuotientMem`).

Lean target: `formal/Midfall/Generator/Quotient/VmTypes.lean`.

## Why the split is by kind and not by size

`vm/reference.rs` - which is `QVM.run` of PLAN 9.5 and the anchor for all of M6 -
imports `QuotientExpr`, `QuotientMem` and all 31 opcode constants from `super::`. It
does **not** need the compiler. Splitting `vm/mod.rs` types-first makes the interpreter
reachable after ~700 lines instead of 4,336. (An earlier version of this plan had the
order backwards; corrected round 13.)

## Hazards

1. **The opcode constants are an ABI with three consumers.** They are shared by the
   compiler, the reference interpreter, and the emitted Yul. PLAN 9.5's
   `qvm_yul_refines` is exactly the claim that the Yul agrees with the interpreter, and
   `vm/reference.rs`'s own doc says the reference-interpreter-to-Yul leg is covered "by
   the opcode and memory-token table conformance tests". **Find those tests and port
   them as gates here** - they are the only existing oracle for the table, and porting
   the constants without them leaves the most load-bearing number set in the QVM
   ungated.
2. **Integer widths.** `QuotientMem` is `Literal(u32) | Token(u8) | TokenOffset(u8,
   u32)`. Lean `Nat` does not truncate. For every field, decide and record at the site
   whether a value outside the Rust width is reachable; if it is, model the truncation
   (release wraps, debug panics - the reference profile is release, see BASELINE.md); if
   it is not, say why. Do not silently widen.
3. **`QuotientExpr` is recursive through `Box`.** Lean needs no box, but note two
   things: any function you write over it must terminate by structure (R10, no
   `partial`), and deep trees may stress `#eval` reduction. If a gate needs a deep tree,
   keep it shallow and say that the depth is not what is being tested.
4. **The shape-recognition invariant.** `QuotientLimbShape`'s doc is explicit: shapes
   "are recognized from the expression tree alone", "adding a limb opcode must never
   make correctness depend on a gate label or on a hand-maintained list of circuit
   gadgets", and "if a shape is not recognized exactly, the builder falls back to
   ordinary Fr VM opcodes". That last clause is a *safety property* worth a gate: a
   mis-recognition must fall back, never mis-evaluate. Port the recognition functions
   with that property gated, and report whether the code actually guarantees it or only
   intends to.
5. **`QUOTIENT_VM_LIMBS = layout::quotient_limb::LIMBS`** - cross-check against the
   accumulator limb constants P-06 landed (`AccumulatorEncoding.supportedNumLimbs` = 7)
   and against `Supported.hLimbs` in PLAN 9.5. If they disagree, STOP and report: that
   is a normative-statement problem, not a porting one.
6. **Do not port the compiler in this package.** The temptation will be to pull in
   `QuotientProgramPlan`'s builder because the record is right there. Keep the boundary:
   types and constants only, so P-09b can land without waiting for 3,600 lines.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` does not apply
lakefile options; line numbers from `git show HEAD:<path>`), `Kzg.lean` and `Vk.lean`
headers for house style and for what auditing inherited claims looks like.

Binding: PLAN section 4 (R1-R11); `Vec` -> `List` in the Generator row; R4 release
profile semantics. **R-41** (perturbations actually run, failures reported), **R-48**
(the shared layout fixture has all-zero PCS bases - build your own or assert distinctness
first), **D-P17** (no theorems in a file importing Instances/; checks.sh enforces).

**No idle builds** - run `lake build` in the background and keep working.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit. Register the module in `formal/Midfall.lean` once it compiles.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from the current base.
- At least 10 gates, including the opcode-table conformance gates from hazard 1 and a
  fallback-not-misevaluation gate for hazard 4.
- Per-gate perturbation evidence, with anything that failed to redden stated plainly.
- A finding on whether the opcode table, the interpreter and the Yul emitter are
  currently kept in sync by anything stronger than a test.

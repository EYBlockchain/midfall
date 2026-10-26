# P-09b - `vm/reference.rs`: the quotient VM interpreter (this is `QVM.run`)

Status: READY - P-09a landed everything it imports. This is the **M6 anchor**: PLAN 9.5's
`def QVM.run (prog) (f) : Except QVM.Fault QVM.Output -- port of vm/reference.rs` names
this file, and `qvm_compile_correct`, `qvm_validated_noOOB` and `qvm_yul_refines` are all
stated against whatever this turns out to be.

Reference: `proofs/solidity-verifier/src/lowering/quotient_numerator/vm/reference.rs`
(549 lines at HEAD). Lean target: `formal/Midfall/Generator/Quotient/VmReference.lean`.

## The thing to understand before porting

This is not just an interpreter. Its module doc says it is the **second implementation**
of the VM ABI, existing so the generator can certify its own output: the emitted bytecode
is executed here and compared against direct evaluation of the `QuotientExpr` trees it
was lowered from, and a disagreement rejects the render. The soundness of that check is
probabilistic and the doc says so - a deterministic challenge is sampled from the
finalized bytecode, constant table, expression trees and VK payload, and a miscompilation
yields a wrong polynomial fixed before the challenge was known, so it disagrees with
probability `1 - deg/|Fr|`.

**Two consequences you must report on, not absorb.**

1. The Rust certifies **emitter -> reference interpreter** only. Its doc states the
   reference-interpreter -> Yul leg is covered "separately by the opcode and memory-token
   table conformance tests and by the per-identity Rust/Solidity trace differential". So
   PLAN 9.5's `qvm_yul_refines` has no proof structure in the reference to mirror - it is
   a theorem we originate. Do not invent a Rust-side argument to hang it on.
2. The doc also says identities executed as inline Yul, native callbacks, or the
   structured tail "are not lowered to bytecode at all", so this module evaluates them
   from their expression trees and they are covered only by the other two mechanisms.
   That bounds the domain of `QVM.run`, and therefore of every M6 statement. State the
   bound precisely in the header; a `qvm_compile_correct` whose domain silently excludes
   the native-callback identities is a different theorem from the one PLAN 9.5 wrote.

## Hazards

1. **`QuotientRefMemory::derive(domain, address)` is the certification's heart.** It is
   a seeded PRNG over a `[u8; 32]` seed, using Keccak (the file imports
   `sha3::{Digest, Keccak256}`). The whole probabilistic argument depends on reproducing
   it byte-exactly: a different derivation is a different challenge distribution and the
   certification silently changes meaning. Port the exact byte layout of the preimage and
   gate it on concrete (domain, address) pairs. `new(seed)`, `literal(ptr)`,
   `token(token, offset)` must be gated together - the memoisation is part of the
   semantics, not an optimisation: the same address must yield the same value across
   calls.
2. **`eval_quotient_identity` (131-349, ~220 lines) returns `Result<_, String>`** while
   PLAN 9.5 wants `Except QVM.Fault QVM.Output`. That is a type change, not a rename.
   Enumerate every error string, decide the `Fault` mapping, and record whether any
   caller inspects the string (if one does, R-43 F2 payload loss applies and you must
   say so).
3. **`fq_from_u256` (545)** - does it reduce mod r or reject non-canonical? Check
   against `Common/Codec.lean` and the R-7 non-canonical-rejection work, and gate it.
   A silent reduce where the reference rejects is an R-30-class divergence.
4. **The `*_form` helpers are the semantics of the shape recognizers** -
   `affine_linear_term`, `affine_product_term`, `limb_linear_form`, `limb_row_form`,
   `limb_pairwise_form`, `modarith7_form` (435-509). `modarith7_form` is the 7-limb
   foreign-field path that `Supported.hLimbs` and PLAN 13's foreign-field paper refer to.
   Expect the accumulator subtleties (coord-1 encoding, sentinel, identity flag) here.
   These are the functions a mis-port would get subtly wrong and a gate would miss, so
   gate each against a hand-computed example, not just against itself.
5. **`byte_at`, `read_u16`, `read_u32`, `const_at` return `Result` on out-of-range**
   rather than panicking - unlike slicing elsewhere in the same crate. Port each
   faithfully; do NOT unify them into one bounds-checked helper, because "returns Err" and
   "panics" differ observably in whether a render is rejected or the build aborts.
6. **The `Q_MEM_*` tokens and opcode bytes come from P-09a.** Use
   `Midfall.Generator.Quotient.VmTypes`; do not re-declare them. If you find yourself
   wanting a validator (`validate_quotient_mem_token`, QVM:2758) or the operand walker,
   those are compiler-side and deliberately absent - report what you need rather than
   pulling the compiler in.

## Rules

Read first: `docs/plans/README.md` standing notes (the `lake env lean` trap; line numbers
from `git show HEAD:<path>`; **register your module** - R-50 made an orphan a hard
failure), and `Quotient/VmTypes.lean` for the current style including the D-P19 pattern.

**D-P19 now binds you**: where a gate's expectation lives in an artifact, read the
artifact at `#eval` time rather than pasting it, and put a reachability gate first.

**R-41** (perturbations actually run inside each gate's scope; report failures to
redden), **R-48** (the shared layout fixture has all-zero PCS bases - build your own or
assert distinctness), **D-P17** (no theorems in a file importing Instances/).

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile (no overflow
panic, `debug_assert!` compiled out; indexing and division-by-zero do panic).

**No idle builds** - run `lake build` in the background and keep working.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit. Register the module once it compiles.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 478 across 36 files.
- At least 12 gates. Required specifically: the `derive` byte-exactness gate (hazard 1),
  one gate per `*_form` helper (hazard 4), and a gate pinning the memoisation property.
- A finding stating the **exact domain** of `QVM.run` - which identity kinds reach the
  bytecode and which do not - because PLAN 9.5's three `qvm_*` theorems are stated over
  it and their wording may need to change.
- A finding on whether the certifier's challenge derivation is reproducible in Lean
  without the compiler (if the challenge depends on finalized bytecode the compiler
  produces, note that `qvm_compile_correct` may need P-09c before it can be stated).

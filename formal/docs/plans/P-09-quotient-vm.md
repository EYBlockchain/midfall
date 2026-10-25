# P-09 - the quotient VM, split into four packages

Status: DRAFT. BLOCKED on P-06 (api: QuotientIdentitySource, the manifest types) and
P-07 (kzg) and P-08 (vk). This is the largest block in the port (~10,000 Rust lines) and
the one PLAN 14.7 names as the weakest estimate, so it is split here rather than fired
as one task.

| pkg | Rust | lines | Lean target | what it gives M6 |
|---|---|---:|---|---|
| P-09a | `quotient_numerator/mod.rs` + `vm/reference.rs` | 561 | `Generator.Quotient.Vm.Reference` | the second implementation: `QVM.run` of PLAN 9.5 |
| P-09b | `vm/mod.rs` | 4,336 | `Generator.Quotient.Vm` | the compiler: program plan, opcode model, shape recognizers |
| P-09c | `vm/certify.rs` + `vm/disasm.rs` | 1,653 | `Generator.Quotient.Vm.{Certify,Disasm}` | the certification and listing leg (Tier-2 by PLAN 14.7) |
| P-09d | `quotient_numerator/yul_emit.rs` | 1,176 | `Generator.Quotient.Vm.YulEmit` | emitting the VM's Yul |
| P-09e | `quotient_numerator/direct/{mod,folds,layout,validate,trace}` + `quotient_direct.rs` | 3,869 | `Generator.Quotient.Direct` | the Direct lowering (M10) |

## The finding that reshapes this block

`vm/reference.rs`'s own module doc says what it is, and it is **not** what PLAN 9.5
assumes when it writes `def QVM.run ... -- port of vm/reference.rs`. It is a
*certifier*: a second, independent implementation of the quotient VM ABI whose purpose
is to let the generator reject its own output before any artifact is produced. The
mechanism is probabilistic, and the doc says so explicitly:

> the certifier samples a deterministic challenge from the finalized quotient bytecode,
> constant table, oracle expression trees, and VK payload, then evaluates the fixed
> program at that assignment. Any miscompilation therefore yields a wrong polynomial
> that was fixed before the challenge was known, and it disagrees with the correct one
> with probability `1 - deg/|Fr|`.

Two consequences, and they are the reason this plan exists in five pieces instead of one.

1. **There is no proof structure in the Rust to mirror.** The doc names the leg it
   certifies (emitter -> reference interpreter) and then says the
   **reference-interpreter -> Yul leg is covered separately** by "the opcode and
   memory-token table conformance tests and by the per-identity Rust/Solidity trace
   differential", and further that identities executed as inline Yul, native callbacks,
   or the structured tail "are not lowered to bytecode at all" and "remain covered only
   by those other two mechanisms". So PLAN 9.5's `qvm_yul_refines` has **no counterpart
   in the reference at all** - it is a theorem we would be originating, not translating.
   Anyone planning M6 by analogy to "what the Rust does" will plan the wrong thing.
2. **The two-implementation pattern is an opportunity, not just a hazard.** The Rust
   already has an emitter and an independent evaluator that it checks against each other
   with a Schwartz-Zippel argument. Porting *both* to Lean and proving them equal turns a
   probabilistic certification into a theorem - which is strictly stronger than what the
   reference achieves, and is the natural shape of `qvm_compile_correct`. Say this
   out loud in the M6 plan so nobody later mistakes the Rust's sampling check for the
   standard we are aiming at.

## P-09a hazards (reference.rs, 549 lines) - to be expanded when it is fired

1. `QuotientRefMemory::derive(domain, address)` (85-113) is a seeded deterministic
   PRNG over a `[u8; 32]` seed. The whole certification argument depends on it being
   exactly reproduced: a different derivation is a different challenge distribution and
   the probabilistic claim silently changes meaning. Byte-exact gate required, and the
   `new(seed)` / `literal(ptr)` / `token(token, offset)` trio must be gated together
   because the caching behaviour is part of the semantics.
2. `eval_quotient_identity` (131-349) is ~220 lines and is the interpreter proper. It
   returns `Result<_, String>`; PLAN 9.5 wants `Except QVM.Fault QVM.Output`. That is a
   type change, not a rename - record how the Rust error strings map to `Fault`, and
   whether any error string is inspected by a caller (if it is, the mapping is
   observable and F2-style payload loss applies).
3. The `*_form` helpers (`affine_linear_term`, `affine_product_term`, `limb_linear_form`,
   `limb_row_form`, `limb_pairwise_form`, `modarith7_form`) are the semantics of the
   shape recognizers. `modarith7_form` (435-509) is the 7-limb foreign-field path that
   PLAN 13 ties to the foreign-field paper and that `Supported.hLimbs` asserts the limb
   count for. Expect the accumulator-limb subtleties (coord-1 encoding, sentinel,
   identity flag) to live here.
4. `byte_at`, `read_u16`, `read_u32`, `const_at` return `Result` on out-of-range rather
   than panicking - unlike the slicing elsewhere. Port each faithfully; do not unify them
   into one bounds-checked helper, because the difference between "returns Err" and
   "panics" is observable in whether a render is rejected or the process aborts.
5. `fq_from_u256` (545) - check whether it reduces mod r or rejects non-canonical, and
   gate it. R-7 and the non-canonical-scalar work make this a live question.

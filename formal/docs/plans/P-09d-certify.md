# P-09d - `vm/certify.rs`: the certifier driver (seed derivation + segment walker)

Status: READY - P-09a (vocabulary), P-09b (interpreter), P-09c (builder) all landed.
365 lines. Chosen over the validator because P-09c identified it as the actual blocker:
`qvm_compile_correct` cannot be **stated** until (a) the identity segment walker and (b)
`derive_certify_seed` exist, and both live here, not in `vm/mod.rs`.

Reference: `proofs/solidity-verifier/src/lowering/quotient_numerator/vm/certify.rs`
(365 lines at HEAD). Lean target:
`formal/Midfall/Generator/Quotient/VmCertify.lean`.

## Why this order

P-09c's required finding: the finalized bytecode now exists in Lean, but the theorem that
quantifies over it still cannot be written because the seed hashes artifacts and the
multi-identity program has no Lean-side segmenter. Both are ~tens of lines here rather
than ~800 lines of validator, so this is the shortest path to a statable M6 theorem.

## Hazards

1. **`derive_certify_seed` is the soundness hinge.** It is Keccak over
   `"midfall/quotient-vm/certify-seed/v3"`, then each build's finalized BYTECODE and
   constant table, then each oracle expression tree hashed with node/address tags
   (QVC:79-111), then the VK payload bytes. Byte-exactness is not optional: a different
   preimage is a different challenge, and the whole "the polynomial was fixed before the
   challenge was known" argument depends on the derivation being exactly the reference's.
   Gate the preimage layout segment by segment, in the style P-09b used for
   `QuotientRefMemory::derive` (independent Python Keccak cross-check is welcome, and
   P-09b already built one you can reuse).
2. **The version tag `v3`** implies earlier schemes existed. Grep for `v1`/`v2` and for
   any test pinning the tag; if the tag is unpinned in the Rust, say so - a silent bump
   would change the challenge distribution without changing any type.
3. **The identity segment walker (QVC:228-245)** slices a multi-identity program into
   per-identity expression subprograms. P-09b established that the interpreter only ever
   sees ONE identity's subprogram, and P-09c supplied only a single-trailing-fold
   stripper. This walker is what makes the per-identity statement cover a real program.
   Gate it by round-tripping a 3-identity built program: segments extracted, each run
   through `QVM.run`, results equal the per-identity oracle values.
4. **The certification comparison itself** (build the program, evaluate at the derived
   assignment, compare against direct evaluation of the `QuotientExpr` trees) is the
   thing PLAN 9.5's `qvm_compile_correct` is the Lean analogue of. Port it, and state
   plainly in the header that the Rust version is **probabilistic** (one sampled
   challenge, `1 - deg/|Fr|`) while a Lean theorem over the same objects would be
   unconditional - do not let the port's gate be mistaken for the theorem.
5. **`QuotientProgramBuild` is produced by P-09c's `finish`.** Use it; do not re-derive.
   If you need the validator (`validate_quotient_program`) to make a claim, report the
   need rather than pulling the validator in - it is the next package.
6. **Absorb P-09c's compaction-scoped copies if and only if they belong here.**
   `quotientOpLen`, `quotientProgramUsage` and friends currently live in
   `Midfall.Generator.QuotientBuilder` as scoped stand-ins (P-09c hazard 7). If the
   general versions are in `vm/mod.rs` rather than here, leave them and say where they
   should land; do not create a third copy.

## Rules

Read first: `docs/plans/README.md` standing notes (`lake env lean` trap; line numbers
from `git show HEAD:<path>`; **register your module** - R-50), and the three Quotient
files for what is available. REVIEW.md R-30, R-38, R-40, R-41, R-48, R-50, and D-P19
(read artifacts at `#eval` time, reachability gate first).

**R-41** binds you: perturbations actually run inside each gate's scope, failures to
redden reported. **R-48**: own fixture or assert distinctness first.

Binding: PLAN section 4 (R1-R11); `Vec` -> `List`; R4 release profile.

**No idle builds.** If you sense you are running low on room, leave the file either
compiling or unregistered - never half-written and registered.

Do NOT edit Rust files, `Statements.lean`, `SORRY.md`, or another package's Lean file.
Do NOT git add or commit.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; KAT count up from 556 across 38 files.
- At least 10 gates, including the seed-preimage gate (hazard 1) and the 3-identity
  segment round-trip (hazard 3).
- **The required finding**: state explicitly whether `qvm_compile_correct` is now
  statable in Lean, and if not, name every remaining missing piece. That is the whole
  point of this package.

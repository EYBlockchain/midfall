# Port review log (plan rule R11)

Rule R11: every module PR carries a checklist mapping Rust line ranges to
Lean defs, signed off by a second agent. The checklists live in the commit
bodies; this file records *who reviewed what*, and - more usefully - every
finding that needs an owner outside the module that surfaced it.

## Standing rule: independent adversarial review per task

User-directed, round 7. **After every completed task within a milestone, a fresh
agent session performs adversarial review and independent verification.** Not a
confirmation pass: the brief must say assume a divergence exists and find it.

This exists because R-31 showed the process was one-sided - every sub-agent package
got reviewed (by the coordinator) and none of the coordinator's own work did, and
both surviving bugs were in the unreviewed half. It has already paid for itself:
the review that followed R-31 found the G1 codec accepting off-curve points and
non-canonical x (proof malleability, falsifying two stated round-trip lemmas), and
found that 31 of the tree's KATs were not CI gates at all.

Practical constraints in this project: one sub-agent at a time, so review competes
with authoring for the same slot and must be budgeted deliberately; and reviewers
must rebuild before evaluating, because a stale .olean made one reviewer about to
report a failing KAT that was actually green.

## Sign-offs

| package | commit | author | reviewer | verdict |
|---|---|---|---|---|
| Common/Bytes codecs | `06f1350` | agent | agent (self) | ok after fixing `Array.qdrop`/`qtake`, which do not exist in v4.35.0 |
| Exec/Transcript + Common/Codec (D-P6) | `b9b7ad5` | agent | - | needs a second pair of eyes |
| Exec/Kzg/{Params,Msm}, Exec/Query (D-P7) | `b6bacf1` | agent | - | needs a second pair of eyes |
| Exec/Arith + Exec/Domain | `05a199f` | sub-agent | agent | **signed off**: provenance on every def, reachability evidence at every skip, KATs hand-checked |
| Exec/Query (CommitmentReference, VerifierQuery) | `b2c536c` | agent | - | see R-7 |
| Exec/Kzg/Utils (construct_intermediate_sets) | `363d2cd` | agent | - | see R-7 |
| Exec/Poly | `451a491` | sub-agent | agent | **signed off**: the reachability result is the deliverable; see R-8 |
| Exec/Kzg/MultiOpen (multi_prepare) | `8df0e05` | agent | - | see R-8, R-9 |
| Exec/Circuit (constraint system) | `95f5d88` | agent | - | see R-12 |
| Exec/Circuit, superseded | `ec1d19e` | sub-agent | agent | **signed off**: fixes two soundness gaps in 95f5d88 (R-17) |
| Exec/{Permutation,Logup,Trash} verifier paths | `b4ad69b` | sub-agent | agent | **signed off**: P1 and P3 re-verified against the Rust by hand |
| Yul/Externals (EIP-2537 / modexp layouts) | `3a8ded1` | sub-agent | agent | **signed off**: it found two real bugs in committed code (R-20) |
| Exec/VerifyingKey, Exec/Linearization | `047b4fb`, `5c221c3` | agent | - | R-1 resolved; see R-18, R-19 |
| Exec/Verifier (parse_trace) | `fbe7ce8` | agent | - | schedule KATs pin byte accounting |
| Spec/Degrees | `7da8cb9` | sub-agent | agent | **signed off** - and it found a soundness gap in §9.4 (R-22) |
| Exec/Accumulator | `782b9a2` | sub-agent | agent | **signed off**: it found §9.5's decodeAcc_injective is false (R-25) |
| Exec/Verifier (verify_algebraic_constraints, prepare) + Exec/Native | `389a0c4` | sub-agent | agent | **signed off**: the frozen §9.2 interface is not implementable (R-27) |
| Exec/Verifier after external review | `1d32d34` | external reviewer + agent | agent | **two real bugs fixed** (R-30) |
| Exec/Verifier after a second audit | (this commit) | external auditor + agent | agent | **one new R8 bug fixed** (R-32); two of its four findings were already logged |
| `msmInnerProduct` closes the deferred item | `a8cf7f2` | agent | - | - |

The Arith/Domain review spot-checked the two claims most likely to be wrong
against the Rust: `g_coset_inv = g_coset.square()` (domain.rs:82 - correct,
and only an inverse because zeta^3 = 1) and the chained `batch_invert` order
(domain.rs:117-124 - t_evaluations, ifft_divisor, extended_ifft_divisor,
barycentric_weight, extended_omega_inv, omega_inv; correct).

## Findings that need an owner outside their module

### R-1 `transcript_repr` needs byte-exact Rust `{:?}` output - RESOLVED (047b4fb)

`EvaluationDomain::pinned` is on the VK construction path (plonk/mod.rs:271,
inside `from_parts`), but only through `Debug` formatting whose bytes feed the
hash that produces `vk.transcript_repr`. Reproducing it faithfully requires
byte-exact `{:?}` for `PinnedEvaluationDomain` *and* `PinnedConstraintSystem`.
Plan Section 1 takes `transcript_repr` as given ("keygen code is out of scope,
`transcript_repr` is taken as given"), so the port can import it from the
exported `vk.json` instead of recomputing it - but that must be a decision,
not a silence, and the conformance harness should assert the imported value
against the Rust one rather than trusting it. Owner: Exec/VerifyingKey.

### R-2 `l_i_range` returns all zeros at a domain point - a soundness hypothesis

At any `x = omega^i`, every `x - omega^r` entry that hits zero is skipped by
`batch_invert` *and* `x^n - 1 = 0`, so `common = 0` and the whole vector comes
back zero rather than `l_i(x) = 1`. The verifier is only correct because the
squeezed challenge `x` misses the domain. That is an unstated hypothesis of
every statement that touches the quotient identity. It belongs in
`Spec/Piop` / the S1 proof as an explicit `x ∉ domain` side condition, and in
`Supported` if the contract needs it. Pinned by a Domain KAT
(`lIRange 13 1 [0,1] == #[0,0]` over `ZMod 17`). The same hypothesis reappears in multi_prepare as a crash rather than a wrong
value: `den.invert().unwrap()` (kzg/mod.rs:479) aborts the process if the squeezed
`x3` coincides with any point of a point set. One unstated assumption, two
failure modes - silent zeros in the quotient identity, hard abort in the
multi-open - and both must be discharged by the same side condition.

Owner: Phase 4.

### R-3 `FieldConsts` is a trust boundary - two properties nothing checks

`rootOfUnity` must be a primitive `2^S`-th root and `zeta` must have order 3
(domain.rs:82 uses `zeta^2` as `zeta⁻¹`). Neither is verified anywhere in the
Rust, and a wrong value silently changes the extended domain and the coset.
When `Assumptions/Pairing.lean` supplies the BLS12-381 `FieldConsts` it must
also supply these two facts as named hypotheses, and the `AdmissiblePairing`
instance must carry them. Owner: Assumptions/.

### R-4 the `n_g2` divergence (G2 twin of D-P5) - conformance must pin it

`ParamsVerifierKZG::read` uses `-G2Affine::generator()`;
`ParamsKZG::verifier_params` uses `-self.g2`. They agree only if the params
file g2 is the canonical generator. `conformance-rs` has to record which path
produced `params.json`, and the baseline freeze should assert the two agree on
the shipped SRS assets. Owner: Phase 3 / Phase 0 step 8.

### R-5 latent panic sites the port keeps as `Fault.panic`

`evals_inner_product` (arithmetic.rs:310, :313), `inner_product` (:272),
`compute_inner_product` (:83), `lagrange_interpolate` (:173, :177, :218, :219),
`EvaluationDomain::new` (domain.rs:53, :98). Plus two the Rust reaches only
through a cast: `min_rotation.abs()` is `i32::abs`, which overflows at
`i32::MIN` (verifier.rs:361), and the slice `&l_i_s[offset..offset+len]`
(verifier.rs:370) panics if an instance column overruns the window. Both are
unreachable for real rotations but must be *argued*, not assumed, when
`Exec/Verifier` is ported. Owner: Phase 2, Exec/Verifier.

### R-6 profile-dependent arithmetic (recorded, not emulated)

`domain.rs:39` `(j-1) as u64` (u32 subtraction: release wraps, debug panics),
`domain.rs:48` u64 multiply, `arithmetic.rs:62` `div_ceil` by zero, and
`MSMKZG::collapse` debug_assert. BASELINE.md fixes the reference profile as
release, so the port follows the release reading and says so at each site.
Owner: none - documented divergence surface.

### R-8 poly::Error is not collapsed uniformly, and the port currently flattens it

Exec/Poly established that `poly/mod.rs` is the prover's polynomial layer: of
526 lines only `enum Error` and `Rotation` are verifier-reachable (Rotation
was already ported), so `Polynomial` is *not* part of L0 and the earlier
planned "`Polynomial` as a record per R9" is withdrawn - porting it would put
prover code in the verifier.

What remains is the error taxonomy, and it is subtler than it looks:

* A short proof gets a different error class depending on *who reads the
  bytes*. `multi_prepare`'s reads are `transcript.read().map_err(|_|
  SamplingError)` (kzg/mod.rs:447, :463, :534) - the `io::ErrorKind` is
  discarded. The plonk verifier's own reads (plonk/verifier.rs:118, :358) go
  through `From<io::Error>` and keep `Error::Transcript(UnexpectedEof)`. Same
  physical failure, two observable classes.
* `verifier.rs:651` collapses every `poly::Error` to `Error::Opening` - but
  only on the `verify_algebraic_constraints` path. The two-phase `prepare()` +
  `Guard::verify()` path that Exec/Native ports (solidity-verifier/src
  /test.rs:370-380) does **not** collapse.
* Our port currently flattens all three variants to `Fault.error
  Error.opening` at Exec/Kzg/Msm.lean (`DualMSM.verify`) and Exec/Kzg/Utils.lean
  (the DuplicatedQuery arm), and keeps the *richer* `Error.transcript ...` in
  `multiPrepare`. So we are lossy at one boundary and too fine at another.

Conformance compares error classes, so this will show up as a mismatch in
Phase 3 rather than as a proof problem. The fix is a decision, not a patch:
either `Fault` gains a `poly (e : PolyError)` constructor - which changes the
plan 9.2 shape `inductive Fault | error | panic` and therefore needs sign-off
(candidate D-P8) - or the port keeps `Error` flat and records the three
variants in the panic-site string, which is ugly but touches no frozen shape.
Recommendation: add the constructor, since the Rust genuinely distinguishes
them and Statements.lean never pattern-matches on `Fault`. Owner: whoever ports
Exec/Verifier, because that is where the collapse lives.

### R-9 `rotate` is unbounded and panics - relevant to Exec/Verifier

Recorded in Exec/Poly but it bites elsewhere: `Polynomial::rotate` (poly
/mod.rs:452-466) uses `slice::rotate_left/right`, which **panic when the
amount exceeds the length**, and nothing bounds `Rotation.0`. Meanwhile
plonk/permutation/verifier.rs:152 constructs `Rotation(-((blinding_factors +
1) as i32))` from caller-controlled blinding factors, and `-rotation.0` at
:457 overflows at `i32::MIN` (release wraps, then `as usize` sign-extends).
`rotate` itself is unreachable in the verifier, but the *rotations it would
receive* are exactly the ones Exec/Verifier and Exec/Permutation must handle
- `l_i_range` and `rotate_omega` take the same values and do not panic, they
just compute large powers. Any `Supported`-style hypothesis that bounds
rotations should cite this.
### R-10 ANSWERED: `verify_final` does NOT batch with the same α as FinalPairing.yul

The plan asked, under the Exec/Accumulator row: "determine whether `verify_final`
batches the accumulator with the same α as FinalPairing.yul (this decides
whether the acc-mode equivalence to Rust is exact)". It does not. Read off the
source:

`aggregation/src/ivc/verifier.rs:143-148` builds `proof_acc` from the DualMSM,
then `Accumulator::accumulate(&[proof_acc, instance.acc])` and one `check`.
`circuits/src/verifier/accumulator.rs:223-239` computes
`r = SpongeChip::hash(as_public_input(acc0) ++ as_public_input(acc1))`,
`rs = [r^0, r^1]`, skips the first, and `accumulate_with_r` (circuits/src
/verifier/msm.rs:166-181) scales the second accumulator's scalars by `r`. So
the *shape* is the same as the contract's: `e(rhs0 + r·rhs1, sG2) ·
e(lhs0 + r·lhs1, −G2) = 1`. But `r` and α are different values:

| | Rust `verify_final` | contract `FinalPairing.yul` |
|---|---|---|
| hash | `SpongeChip::hash` - the POW2 sponge over the native field | `keccak256` |
| preimage | `as_public_input` of each accumulator, i.e. the foreign-point limb | `tag ++ vk_digest ++ kzg_rhs ++ kzg_lhs ++ acc_rhs ++ acc_lhs` |
|  | encoding (lhs then rhs), no vk_digest | in EIP-2537 padded form, **with** vk_digest |
| reduction | sponge output is already a field element, then `truncate_off_circuit` | `mod(keccak256(..), r)`, then `0 -> 1` |
| scaling order | first accumulator un-scaled, second by r | kzg un-scaled, acc by alpha - same order |

Consequences, in order of importance:

1. The `h : g.cfg.accumulator = none` hypothesis on `lowering_equivalence_noAcc`
   and `end_to_end_noAcc` is **necessary, not cosmetic**. In accumulator mode the
   contract and the Rust verify different predicates. Each is individually
   sound - a random α makes the bad pair a single-root event - but they are not
   the same single root. Concretely, write X for the kzg pairing product and Y
   for the acc one; the Rust accepts iff X·Y^r = 1 and the contract iff
   X·Y^α = 1. Pick any Y ≠ 1 and set X := Y^{−r}: the Rust accepts and, since
   α ≠ r, the contract rejects.
2. `lowering_equivalence` as stated in §9.5 is still fine in acc mode, because
   its right-hand side is `ContractRef.accepts`, which is defined with the
   contract's own keccak-based `alphaOf`. The equivalence is contract-vs-Lean-
   reference, not contract-vs-Rust. Do not strengthen it to the Rust.
3. S5's `alphaOf` preimage must keep `vk_digest` (added by curated item 8,
   audit I-7). The Rust has no vk_digest in its batch hash at all, so the
   contract binds α to the verifying key and the Rust does not - a place where
   the contract is *stronger* than the reference. Worth stating as a remark in
   docs/security.tex rather than hiding.
4. Conformance: for accumulator-mode fixtures the harness must compare the
   contract against `ContractRef.accepts`, never against `verify_final`, or it
   will report spurious mismatches. Owner: Phase 3.

Owner of the follow-on decision (does any statement claim acc-mode agreement
with Rust at all?): Phase 4 / whoever writes Spec/Piop.
### R-11 the pairing orientation: the swap is at the CALL SITE, not in the layout

The amended plan cited "AssemblyHelpers.yul:213-232 lays out
`[RHS|G2|LHS|NEG_S_G2]`". Two corrections, and the second is the one that
matters:

1. That line range is the modexp batch-inversion helper. The pairing buffer is
   built in `function ec_pairing(success, lhs_mptr, rhs_mptr)` at
   **AssemblyHelpers.yul:269-287**, and it lays out
   `[lhs_mptr | G2_BASE | rhs_mptr | NEG_S_G2_BASE]` - i.e. **lhs first**, the
   opposite of what the citation said.
2. The RHS-first order is produced at the **call site**:
   `FinalPairing.yul:88` is `ec_pairing(success, PAIRING_RHS_MPTR,
   PAIRING_LHS_MPTR)` - the DualMSM *right* is passed as the function's
   `lhs_mptr`. So the equation the precompile actually evaluates is
   `e(PAIRING_RHS, G2) * e(PAIRING_LHS, -sG2) = 1`.

With `PAIRING_LHS = pi` and `PAIRING_RHS = final_com - v*G + x3*pi`
(FinalPairing.yul:76-77) and the Rust `DualMSM::check` =
`e(left, sG2) * e(right, -G2) = 1` with `left = pi`, `right = final_com`
(plus the scaled_pi term), the two sides are mutual inverses: writing
X = e(pi,G2)^s and Y = e(final,G2), the Rust checks `X / Y = 1` and the
contract checks `Y / X = 1`. So the reorder lemma in §6 is TRUE, and the plan's
form of it - contract `e(right,G2)·e(left,-sG2)=1` - is the right form. But it
is true only because of a naming swap at a call site, which is exactly the kind
of thing a proof gets backwards. Phase 4 should prove the lemma from the
call-site line, and `pcs_spec`'s "PAIRING_LHS/RHS = DualMSM left/right" should
cite FinalPairing.yul:88 as the place the orientation flips.

Also noted while reading: `ec_pairing` compares the precompile output against
1 rather than masking the low bit, because `and(ret, word)` would accept any
odd word; EIP-2537 only returns 0 or 1. And a failed pairing staticcall
*fails closed* with ERR_PRECOMPILE_FAILED, distinct from ProofRejected (MF-4)
- relevant to the plan's §1 EIP-2537 assumption, since it means an unavailable
precompile is a different observable event from a rejected proof, and the
`Eip2537.Holds` hypothesis in L1 must say which one it rules out.
### R-12 the virtual-selector panic is not where the plan says it is

Plan §4's module map row for plonk/circuit.rs says "`evaluate` (a virtual
selector panics)". `Expression::evaluate` (circuit.rs:907-1013) is a pure
ten-way dispatch and cannot panic: it takes the selector reading as a
parameter. The panic is in the *caller's* closure - plonk/verifier.rs and
plonk/evaluation.rs pass a `selector_column` that unwraps the simple
selector's fixed column, and a virtual selector has none. So the site belongs
to Exec/Verifier, not Exec/Circuit, and `Exec/Circuit` deliberately does not
carry a `Fault`-returning evaluate. Recorded so the panic is ported exactly
once. Owner: Exec/Verifier.
### R-13 two reachable panics before a single proof byte is read

Found while porting circuit.rs, and both are on the *verifier* path, reached
from `blinding_factors` / `degree` - i.e. during VK construction or challenge
squeezing, not during proof checking:

* `logup.rs:237` computes `(max_degree - 1) / lookup_degree` where
  `lookup_degree` is the max input degree with `unwrap_or(1)`. The `unwrap_or`
  only fires on an **empty** iterator, so a lookup whose input expressions are
  all constants or challenges has max degree 0 and the division is by zero.
* `logup.rs:318` and `:329` call `slice::chunks(nb)`, which **panics on nb = 0**,
  reached whenever an input expression is as steep as the system degree (a
  degree-3 input in a degree-3 system gives `(3-1)/3 = 0`).

Both are `Fault.panic` in Exec/Circuit. Neither is a soundness problem, but both
mean a malformed-but-parseable VK can abort the verifier, which matters for the
contract: on-chain that is a revert, so the contract and the native verifier
still agree on the outcome, but the conformance harness will see a panic where
Rust sees a panic and Lean sees `Fault.panic` - fine - while a *third* path
(the generator's plan-time degree arithmetic) may not. Owner: Exec/Verifier and
the `Supported` predicate.

### R-14 `verifier.rs:400-411` can index past the end of a Vec

The verifier reads `num_fixed_columns - num_simple_selectors` fixed evaluations
and then, while iterating `fixed_queries`, does `fixed_evals.insert(idx, ONE)` to
fill the missing places. The two lengths need not agree: `fixed_queries` counts
distinct (column, rotation) pairs, which is >= the number of columns, so `idx`
can exceed `Vec::insert`'s bound and abort. This is a real reachable panic site
for a circuit with a fixed column queried at two rotations. Exec/Verifier must
port it as `Fault.panic` and the `Supported` predicate should say whether the
deployed VKs avoid it. Owner: Exec/Verifier.
### R-2 now has THREE manifestations (was two)

The single unstated hypothesis - the squeezed challenge misses a finite set of
bad points - shows up three times, with three different failure modes:

1. `l_i_range` (domain.rs:463): silently returns **all zeros** at a domain point
   (`batch_invert` skips the zero denominator *and* `x^n - 1 = 0`).
2. `multi_prepare` (kzg/mod.rs:479): `den.invert().unwrap()` **aborts the
   process** if x3 coincides with a point of a point set.
3. `logup.rs:460`: `product * f.invert().unwrap()` **aborts the process** when
   any `f_j(x) + beta = 0`. The partial products are computed by inverting the
   full product rather than by a zero-safe prefix/suffix recurrence, so one
   zero factor kills the verifier instead of rejecting the proof.

For (3), `beta` is squeezed *before* the helper polynomials are committed, so an
honest prover is safe - but a malicious prover can aim at it, and on the native
path that is a process abort rather than a rejection. On-chain an abort is a
revert, so the observable outcome differs between the two implementations,
which is exactly what §9.5's observational equivalence has to absorb. Phase 4
must discharge all three from one side condition. Owner: Phase 4 / Spec/Piop.

### R-9 widened: the rotation cast truncates *and* negates wrapping

`permutation/verifier.rs:152` is `Rotation(-((blinding_factors + 1) as i32))`.
That is a **truncating** `as i32` followed by a **wrapping** negation, not just
the `i32::MIN` overflow first noted: `blinding_factors + 1 = 2^31` yields the
rotation `-2^31` (and `rotate_omega` then computes `omega_inv^(2^31)`), and
`2^32 + 5` yields `5`. The only thing bounding it is
`ConstraintSystem::blinding_factors`' `i32::MAX` panic (circuit.rs:2510), now
ported - so the truncation is unreachable *through that path* but live for any
hand-built `Nat`. Exec/Permutation emulates it exactly (`wrapI32`, `asI32`,
`negI32`) with a KAT. Any `Supported` bound on rotations should cite this.

### R-15 lazy-zip asymmetry in the permutation expressions

`permutation.rs:242-277`: the left product is `columns.map(..).zip(permutation
_evals)`, so `get_any_query_index` runs for at most `min(columns,
permutation_evals)` columns, while the right product maps over **all** columns.
With 2 columns and 1 permutation eval the two sides have different factor
counts, and a bogus second column panics on the right but is never looked up on
the left. **This is the one place in the port where being eager instead of lazy
changes the observable result.** Pinned by `expressionsLazy_kats_ok`. Related:
`permutation.rs:236-240` zips sets x column-chunks x permutation-eval-chunks,
so the shortest wins and whole identities are dropped silently, no error.

### R-16 three ordering traps the QVM depends on

Not style: these decide the order identities are batched into the quotient
numerator, so the generated QVM and the reference verifier disagree if any is
ported the other way.

* `permutation/verifier.rs:173` is `.enumerate().rev().skip(1)` - **reverse
  before dropping**. The `omega^last` openings come out in DESCENDING set
  order and the set dropped is the last one, not the first. Re-verified
  against the source. An ascending port is silently wrong: it changes the
  point-set layout and therefore x1..x4.
* `permutation.rs:203-281` chains `[first-set l0*(1-z), last-set (z^2-z)*l_last,
  cross-set, per-set products]` - the last-set constraint comes **second**.
* `trash.rs:84` is a **left** fold, so the first constraint carries the
  **highest** power of the trash challenge (Horner).

Also: `read_product_commitments` reads one commitment per **chunk** of columns
(`chunk_len = cs_degree - 2`) and discards the chunk contents, and
`Committed::evaluate` reads `3k - 2` scalars with the last set's
`last_eval = None`; `k = 0` reads nothing. Re-verified against the Rust. Owner:
M6 (QVM) must cite all of these.

### R-3 extended: `delta` is a fourth unchecked constant, and FieldConsts lacks it

`permutation.rs` uses `F::DELTA`, the coset shift for the sigma polynomials.
Like `zeta` and `rootOfUnity`, nothing checks it: the argument needs `delta^i`
distinct across the chunk range, i.e. `delta` of order at least the number of
columns, and `delta != 0`. `Exec/Arith.FieldConsts` carries `numBits`, `s`,
`rootOfUnity`, `zeta` but **not** `delta`, so `Permutation.expressions` takes it
as an explicit parameter. Follow-up: add `delta` to `FieldConsts` or to
`Assumptions/Pairing` with its order hypothesis, so no caller can pass a `delta`
that collapses the sigma shifts. Owner: Assumptions/.

### R-17 the Circuit re-review, and what it caught

`95f5d88` (my Circuit) was superseded by `ec1d19e`. Two real defects, both
soundness-shaped:

* my `Any.advice` carried no payload, so `query_advice_index` would **merge
  same-index advice columns from different phases** during query dedup - a
  wrong query table, hence a wrong verifier.
* my `nbParallelLookupsPerChunk` mapped an all-zero degree list to 1, which
  **hid the R-13 division by zero** instead of exposing it.

Recorded because it is evidence the R11 second-signer rule does work, and
because it says what a reviewer should actually check: payload types that look
cosmetic, and `unwrap_or` defaults that silently change a divisor.

### Naming pin (fragile interface)

Exec/{Permutation,Logup,Trash} are pinned to Circuit's names as of `ec1d19e`:
`LogupBatchedArgument`, `LogupChunkedArgument`, `TrashArgument` (flattened into
`Midfall.Halo2`, not nested namespaces), plus `ConstraintSystem.getAnyQueryIndex`,
`Column.columnType`, `Expression.Callbacks`, `mapExceptArray`. Renaming any of
those breaks three files. For Exec/Verifier: `ConstraintSystem.degree` and
`blindingFactors` now return `Except Fault Nat`, so callers must thread them;
`CommitmentLabel` has no `BEq` (Exec/Query), so label comparison needs a match;
and `permutation::VerifyingKey::read/write/bytes_length` remain unported - the
VK binary serde is reachable only from plonk/mod.rs:105/185/220, which nothing
in the reachable set calls, so conformance must import the VK as JSON after all
(which is what plan §5 says anyway). Owner: Exec/VerifyingKey.
### R-18 `CommitmentLabel` now derives BEq, which is more faithful than before

Exec/Query declared CommitmentLabel without an equality instance on the grounds that
the port needs only equality "which an inductive has" - but Lean does not auto-derive
BEq, so label comparison needed a match everywhere (the Permutation/Logup/Trash
package hit this as its note N4). The Rust derives `PartialEq, Eq, Hash` at
query.rs:11, so `deriving BEq` is the faithful reading, not an improvement. Added in
5c221c3.

### R-19 the linearization MSM's term order comes from a BTreeMap, not insertion order

`linearization/verifier.rs:73-94` groups the identity multiples into a
`BTreeMap<Option<usize>, F>` and then **iterates** it, so the point/scalar/label
vectors are emitted in key order: `None` first, then `Some` ascending. Two
consequences. (1) The `None` bucket - fully evaluated identities - is visited first
and folds into `expected_eval` rather than contributing a point, so the surviving
terms are ordered by column index regardless of the order the identities came in.
(2) The y powers are accumulated while walking `expressions` in **reverse**
(:75), so the last identity gets y^0 and the first gets y^m. Both are invisible on
a one-identity circuit and wrong in general; both are pinned by a KAT. This is the
same class as R-16 and should be cited alongside it when the QVM batching order is
proved. Owner: none - handled, but Phase 4's linearization lemma must reproduce it.
### R-20 two bugs in committed code, both found by a downstream port cross-checking the source of truth

This is the most important entry in this file, and not because of the bugs.

**The bugs.**

* `Common/Bytes`: `wordToBytesBE` and `natToBytesBE` shared the little-endian
  accumulator, so the BE pair was identical to the LE pair. Consequences:
  `Transcript.squeeze` returned the digest bytes **reversed**, so every squeezed
  challenge in the port was wrong, and `Codec.frToInputBE` absorbed scalars
  little-endian instead of big-endian. Verified before the fix:
  `natToBytesBE 0x01020304 4 = [4,3,2,1]` and `bytesToWordBE (wordToBytesBE 1) = 2^248`.
* `Assumptions/Pairing`: `pBase` was the BLS12-**377** base modulus (385 bits,
  congruent to 1 mod 4), not BLS12-381's (381 bits, congruent to 3 mod 4 - the
  value EIP-2537 states and relies on for square roots). The two moduli share a
  50-digit prefix, so the slip is invisible to the eye.

**Why the gates did not catch them.** Every existing check compared
`wordToBytesBE` against itself: `transcriptKat_reseed` asserts
`t.state == d` and `transcriptKat_chain` asserts
`d2 == wordToBytesBE (keccak256 t.state)`. Both are self-consistent under any
permutation of the byte order, so both stayed green while the transcript was
wrong. That is the general failure mode of round-tripping a function against its
own definition: it proves nothing about orientation. The fix is a check against a
constant the implementation did not produce - `keccak256("")` as 32 named bytes,
`0xfe mod 17 = 16`, the EIP's own modulus - and those are now in
`scripts/checks.sh`, not just in a file nobody runs.

**The process lesson.** Neither bug was found by a reviewer reading the port. Both
were found by an agent porting a *different* module (Yul/Externals) against the
EIP texts and the generator's rendered constants, which forced an independent
derivation of the same numbers. Cross-module porting is a review mechanism; it
should be treated as one deliberately rather than as a side effect of parallelism.

### R-21 three corrections to the Phase 5 brief, from the EIP and the generator

The agent implemented the sources of truth over its instructions, correctly:

* G1MSM frames **interleave** `(point, scalar)` pairs of 160 bytes
  (`AccumulatorHelpers.yul:300-303`, EIP-2537 "160*k ... k slices"); they are not
  `0x80k` points followed by `0x20k` scalars. The two have the same total length,
  so a length-only validity check passes while decoding to different pairs.
* G1ADD input is `0x100` (two padded points), not `0x80`.
* modexp output is exactly `modsize` bytes (EIP-198 plus revm's
  `left_pad_vec(&output, mod_len)`), not padded up to a multiple of 32. All
  generated frames use modsize 32, so the verifier is unaffected - but a
  differential test against a non-32 modulus would diverge.

Also recorded: `MODEXP_GAS = 4080` is a deliberate **bound**, not the price of the
emitted frame (EIP-7883 exact for exponent r-2 is 4064), and the pinned revm
prices modexp with the berlin formula, so neither EIP-7883 nor EIP-7823 is
reachable from the M4 revm differential at all. That is a real limitation on what
M4 can certify. Owner: Phase 3/5.
### R-22 BLOCKER for S1/S3: under `truncated-challenges` the x1 and x4 rows of §9.4 are not provable as stated

**This is the most important entry in this file.** It was found by the Spec/Degrees
agent while deriving the point-set counts from the ported code, and I re-verified
every step against the Rust independently:

1. `truncate` (utils/arithmetic.rs:247-252) takes the low `nb_bytes` of the
   little-endian repr, reads it as an integer and re-embeds it in the field. For the
   scalar field `nb_bytes = ceil(ceil(255/8)/2) = 16`, so `truncate(x)` is the low
   128 bits of the canonical representative of x.
2. `truncated_powers(base) = powers(base).map truncate` (arithmetic.rs:255-257) - so
   the j-th coefficient is `truncate(base^j)`, i.e. `(x^j mod r) mod 2^128`.
3. Those are the batching coefficients: `powers_x1 = truncated_powers(x1)`
   (poly/kzg/mod.rs:393-394) and `powers = truncated_powers(x4)` (:501-502 and
   :520-521).
4. `plonk/verifier.rs` contains **no** `truncate` at all - theta, beta, gamma,
   trash, y and x are full `digest mod r` values. The feature is applied per-round,
   not globally.

Consequence. The x1 batching equation the verifier checks is
`sum_j truncate(x1^j) * C_j = 0` in Fr. That is **not a polynomial equation in
x1**: the coefficients are not polynomials in x1, they are truncations of powers.
So the Schwartz-Zippel step that justifies `roundErr .x1 = chalMass(maxPolysPerSet)`
and `roundErr .x4 = chalMass(numPointSets + 1)` does not apply, and neither does
any degree-count argument for those two rows. `Features.solidity` has
`truncatedChallenges := true` (BASELINE.md), so this is the *deployed* profile,
not an exotic one. S1 and S3 as written in §9.4 are therefore unproven for the
configuration the project is about.

This is not obviously unsound - a truncated challenge still looks like ~128 bits
of randomness per test, so the real bound may well be about 2^-128 per round - but
it is a *different* bound with a *different proof*, and `maxPolysPerSet` is not
the right quantity in it. Per plan Section 12 I am reporting it rather than
quietly restating §9.4.

Options, needing a decision:
  (a) drop `truncated-challenges` from the supported profile - cheapest for the
      proof, but it is what the Moonlight deployment uses, so it would exclude D1;
  (b) re-derive the x1 and x4 rows for truncated powers (paper proof, likely a
      2^-128-per-test argument over the truncation image rather than a degree
      bound);
  (c) keep the degree rows only for `truncatedChallenges = false` and state S1/S3
      with that hypothesis, leaving the deployed configuration unproven.
Recommendation: (b), with (c) as the fallback if the paper proof resists. Owner:
you + docs/security.tex (plan Section 10 step 1, which does not exist yet).

### R-23 three smaller corrections to §9.4's error budget

* `chalMass` is applied per *feature* but the Rust truncates per *round*. For the
  six untruncated rounds (theta, beta, gamma, trash, y, x) the plan's `s / 2^128`
  is about 2^127 looser than the truth - sound, but it throws away 127 bits of
  budget for free. For `x3`, which IS truncated (kzg/mod.rs:456-457), the true
  per-value mass is `3*ceil(r/2^128)/2^256 ~ 1.5/2^128`, so `s/2^128` is **short
  by a factor of about 1.5** - i.e. not an upper bound. Fix: `2*s/2^128`, or state
  the mass as `ceil(3*ceil(r/2^128))/2^256`.
* `roundErr .x3 = chalMass(maxSetSize * n)` can be smaller than the honest bad
  set. x3 must avoid both the n-th roots of unity (n points) and every distinct
  opening point (the denominator factors at kzg/mod.rs:478). With all-singleton
  point sets the plan gives `n` and the truth is `n + numPointSets`. Spec/Degrees
  keeps the plan formula verbatim and defines `badPointsX3Count` beside it; the
  two must be reconciled before S1 is stated.
* `srsBound = 2^extended_k = nextPowerOfTwo(n*(cs_degree-1))` may be **too small**:
  if the proof needs `N >= n*(cs_degree+1)` then for d=3, n=16 the plan's bound is
  32 while 64 is needed, and S1's `hN : idx.srsBound <= N` would not guarantee
  enough SRS. The Rust never states a verifier-side SRS requirement, so this is a
  paper-proof decision, not a code one.

### R-24 duplicated `Chal` / `chalMass`

`Midfall.Security.Chal` and `chalMass` already existed in Security/Challenges.lean
(over `ENNReal`); Spec/Degrees now defines `Midfall.Halo2.Spec.Chal` and `chalMass`
per §9.4's namespace. Both exist with the same intent and different types.
Statements.lean imports the Security one and mentions neither `roundErr` nor
`chalMass`, so collapsing them is free - but it must happen before S1 is stated,
or the two will drift. Also note §9.4 lists **ten** Chal variants, not eleven: the
transcript has no eleventh squeeze once user challenges are excluded by
singlePhase. Owner: Phase 4.
### R-25 BLOCKER for §9.5: `decodeAcc_injective` is FALSE for the contract's decoder

Plan §9.5 states, as a building block of `lowering_equivalence`:

    theorem decodeAcc_injective : decodeAcc enc i₁ = some a → decodeAcc enc i₂ = some a →
      accWords enc i₁ = accWords enc i₂

It is not true, and the reason is in the deployed contract, not in the port. I
verified the Yul directly: `AccumulatorHelpers.yul:130-141`, inside `load_acc_point`, reads

    if is_id {
        // When the flag is set the circuit leaves x and y unconstrained
        // ("can be anything"), so they carry no meaning and must not be decoded
        // or range-checked here.
        mstore(dst, 0) ... four zero words ...
    }

So when the identity flag word is 1, the coordinate words are **neither decoded nor
range-checked**: they are discarded and replaced by the EIP-2537 all-zero identity.
Two instance tails that differ only in the coordinate words of an identity-flagged
side decode to the same accumulator. The agent's `accIdentityKats_ok` exhibits a
concrete pair (flag = 1 with coordinates 12345 / 54321 versus the canonical p-1 /
p-1 encoding - both decode to 128 zero bytes).

**This is malleability of the public input, not a soundness break in the proof
system.** The point is that the circuit genuinely does not constrain those words,
so accepting them cannot let an adversary forge: the decoded accumulator is the
identity either way, and the pairing check sees the same group element. But it
does falsify the statement as written, and §12 says report rather than weaken.

**The fix.** `decodeAcc_injective` survives if `accWords` projects the coordinate
words away for identity-flagged points - i.e. the normalisation is part of the
equivalence rather than of the decoder. Concretely:

    accWords enc i := for each point, if flag = 1 then (0, 0, 1) else (x, y, 0)

with the flag kept. That makes injectivity true and also makes `calldata_canonical"
statable for the accumulator part of the calldata, which §13 already worries about.
Owner: §9.5 needs sign-off for this change of meaning; the port already supports it
(`decodeAcc` returns the MSM-shaped accumulator with the carried scalars un-folded,
so equality of accumulators is decidable at the right level).

### R-26 nine further Rust-vs-contract divergences in the accumulator path

Beyond R-10 (different batching scalar) and R-11 (left/right order), the
Exec/Accumulator port found seven more. The first three change what a correct
statement has to say:

1. **Truncation reaches the accumulator too.** Under the deployed profile the Rust
   truncates its powers (`accumulator.rs:229-230`, `truncate_off_circuit`) while the
   contract's alpha is a plain `mod r` (`FinalPairing.yul:30`). So the two differ in
   more than the hash function - relevant to R-22, since this is a third site where
   truncation changes the algebra.
2. **Shape assumption in the decoder.** The contract's decoder reads
   point, scalar, point, scalar, tail - exactly one base and one scalar per side
   (`yul:211-280`). The Rust's `as_public_input` emits ALL bases, then ALL scalars
   (`msm.rs:213-215`). They agree only for a *collapsed* accumulator; a
   non-collapsed one exported through that path would be read against the wrong
   slots **silently**. `decodeAcc_encode` is therefore only statable for collapsed
   shapes, and `fullyCollapsedPublicInputWords` exists to say when.
3. **Negation is represented oppositely.** The circuit's fixed base for "-G" is the
   negated generator (`verifier/mod.rs:119`); the contract embeds the POSITIVE base
   from the VK header and negates the public scalar instead
   (`artifacts.rs:200`, `yul:322-326`) - and rejects `s ≥ r` BEFORE negating,
   because `mod(sub(r,s),r) ≠ -s` for a non-canonical `s` (`yul:319-321`). Same
   group element, opposite representation; a proof that reasons about the fixed-base
   tail must pick one and say so.
4. The contract curve-AND-subgroup-checks every decoded accumulator point (G1MSM at
   `yul:246`, `:357-365`); the Rust never validates accumulator points, since they
   come from `DualMSM::split` over already-checked commitments. The contract is
   strictly stronger here - same direction as R-10's consequence.
5. Wrong-length instance arrays fail closed through three separate mechanisms, none
   inside the decoder: generation-time `validFor`, call-time `VkLoading.yul:102-108",
   and - if both were bypassed - reading zeros, which under the coord-minus-1
   encoding decodes to coordinate 1, an off-curve point the precompile rejects.
6. The contract separates a failed decode from a failed precompile (`precompile_failed`,
   `yul:184-189`, MF-4) and skips the G1MSM calls once out is false. `Option`
   collapses both to `none`: gas differs, the decision does not.
7. Non-canonical instance words (≥ r) are rejected by the contract (`yul:226`, `:290`,
   `:321`) but `Fr p = ZMod p` cannot represent such a word, so that rejection is
   expressible only in the `Array Word256`-typed decoder. The port therefore types
   `decodeAcc` over raw words and lifts `Array (Fr p)` through `frWord`, which loses
   exactly that rejection - documented at `frWord`, and the same gap §13 records for
   `calldata_canonical`.

Also recorded: the pairing-batch domain tag is a 29-byte literal left-padded by
`mstore` (`layout/mod.rs:330-331`), not right-padded ASCII - easy to get wrong when
reimplementing `alphaOf`; and `decodeAcc` needs four arguments (encoding, codec,
generated fixed-base list, instance words) where §9.5 writes two, the extras forced
by D-P1/D-P6 and the per-VK generated base list. Whoever writes the real
`ContractRef.accepts` must supply them - `Lowering/Types.lean` currently has only the
no-accumulator arm.
### R-27 BLOCKER for M2: the frozen §9.2 interface cannot be implemented

**Status update:** D-P9 has been adopted. `VerifierEnv` now bundles the G1 codec,
field constants, delta, and runtime switch; `Statements.lean` has been re-pinned
and its digest updated. `prepare` and `verifyNative` are implemented through that
environment. The historical blocker below is resolved at the interface level,
but conformance remains blocked by the KZG read-schedule exposure needed by
`decodeRust` and the hash-parameterised transcript needed by `prepareMsgs`.

Plan D6 freezes `Midfall/Statements.lean` and CI checks its hash. The §9.2 signatures
in it are not implementable against the port, so the four `Exec/Native` sorries cannot
be removed without re-pinning that file. The agent verified this by trying both ways
against the real file, not by reasoning about it:

| missing from §9.2 | why every leaf needs it |
|---|---|
| \`G1Codec G₁\` (D-P6) | every commitment read or absorb needs \`ofCompressed?\` and \`toEip\`; \`parseTrace\`, \`hashableG1\`, \`multiPrepare\`, \`Pcs.kzg\` and Exec/Accumulator all take it explicitly |
| \`FieldConsts (Fr p)\` (R-3) | \`multi_prepare\` needs \`NUM_BITS\` for \`truncate\`/\`truncated_powers\` (kzg/mod.rs:394,457,502,521), and truncation is ON in the deployed profile (R-22) |
| \`delta : Fr p\` (R-3 extended) | \`FieldConsts\` has no delta, so \`partiallyEvaluateIdentities\` takes it and every caller must thread it |

Explicit parameters fail at \`Statements.lean:43\` with "the argument F has type
\`Features\` but is expected to have type \`G1Codec ?m\`"; instance-implicits fail
because \`G1Codec\` is a structure, not a class, and \`Statements\` binds only
\`AdmissiblePairing\` anyway.

**The trap the agent correctly refused.** A degenerate \`G1Codec\` for an abstract group
(every read returns \`none\`, every absorb the empty input) *is* writable and *does*
compile, so \`verifyNative_iff_msgs\` would elaborate while the verifier rejects every
proof. That is precisely the failure mode plan §12 exists to prevent, and it would
have looked like progress. The sorries stay, registered as blocked, with the complete
bodies in \`prepareWith\`/\`verifyNativeWith\` waiting on a re-pin.

Three further §9.2 problems that a re-pin must also fix, independent of the arity:

* \`decodeRust F vk π\` **cannot be schedule-driven**: the schedule depends on
  \`committed_instances\` and \`instances\` (one eval per committed instance column at
  verifier.rs:357-358, one advice block per proof at :379-381), neither of which it
  takes. \`verifyNative\` hard-codes the solidity shape, so the iff is only statable
  with that shape as an explicit hypothesis.
* It also cannot see \`multi_prepare\`'s own reads (\`f_com\`, the \`q_evals_on_x3\`
  block, \`π\` at kzg/mod.rs:447,463,531) because \`multiPrepare\` returns only the
  DualMSM. Either Exec/Transcript gains a read-recording hook or MultiOpen exposes
  its read shape.
* ~~\`verifyMsgs_iff_spec\` quantifies over an arbitrary \`H : Hash\` while
  \`Transcript.squeeze\` hard-codes keccak256~~ **RESOLVED** (\`972c6b2\`):
  \`Transcript\` now carries \`hash : Bytes → H256\` defaulting to keccak256, with
  \`Transcript.initWithHash\`, so rule R9's "hash is a parameter everywhere" holds
  and §9.5's hash-agnostic lowering proofs have something to instantiate. What
  remains is a boundary, not a gap: the Rust's Blake2b transcript (64-byte output,
  distinct common/challenge prefixes) is unmodelled, and plan Section 1 excludes
  transcripts other than Keccak.
* ~~\`decodeRust\` cannot see \`multi_prepare\`'s own reads because \`multiPrepare\`
  returns only the DualMSM~~ **RESOLVED** (\`972c6b2\`): rather than expose the KZG
  read shape, \`Transcript\` now logs every read as \`(width, raw bytes)\` and
  \`decodeRust\` reports what the pipeline actually consumed. One schedule, not two
  that must be proved to agree - duplicating it is the R-30 / R-32 failure mode.

**STATUS: the arity blocker is resolved.** D-P9 was adopted and §9.2 re-pinned with
a bundled \`VerifierEnv\` (codec, field constants, \`delta\`, runtime switch), and
\`decodeRust\` gained the \`inst\` argument the schedule actually depends on. All four
\`Exec/Native\` definitions are executable and \`Exec/\` has zero sorries; what remains
of M2's acceptance is the conformance harness itself (Phase 3), not the port.

The port itself is complete - every
Rust line on the verifier path now has a Lean counterpart or a documented skip.
Owner: you (candidate D-P9 in docs/design.md).

### R-28 no model of `AdmissiblePairing` exists, so nothing on the pairing path runs - RESOLVED (`2d9a3b0`)

A consequence of D-P1 that nobody had priced: the port is abstract over
\`AdmissiblePairing G₁ G₂ Gₜ\` and there is **no instance anywhere in the tree**. So
\`verifyAlgebraicConstraints\` and \`prepare\` are type-correct but not runnable, and
no fixture can be fed to them. That blocks not only conformance (M2) but the revm
differential (M4) and every KAT that would want to evaluate a real pairing.

This is not an argument against D-P1 - abstraction is what lets the theorems state
cleanly - but it means the plan needs a fourth track: a concrete BLS12-381 instance,
or at least a small abstract model good enough to execute on, before M2 can close.
Owner: Assumptions/. Worth deciding alongside R-27, since a re-pin of §9.2 is the
natural moment to say what the executable instantiation looks like.

### R-29 two corrections to my own brief, and a tooling bug

The agent followed the source over its instructions in two places where **I was wrong
in the brief** (recording this because the briefs are load-bearing):

* I wrote that verifier.rs:260-268 re-checks \`is_empty\` \emph{and} uniform row
  length. It re-checks only \`is_empty\` (:263-265); the uniform-row check is :54-58
  and the column-count check :61-65, both in \`parse_trace\`. So
  \`verify_algebraic_constraints\` does **not** re-validate the instance column count,
  which is what makes the :366 index panic reachable.
* I wrote "the seven \`.zip\` calls"; there are six \`.zip\` calls producing seven
  components.

Tooling: \`scripts/lean_grep.py\` opened a block comment only on \`/--\`, never on
\`/-!\`, so prose inside a \`/-! ... -/\` note that spelled the word \`sorry\`
registered as a **false proof hole** - it did, at Native.lean:75, and the agent
worked around it by not spelling the word rather than by hiding a hole. Fixed: the
opener test now accepts \`/--\`, \`/-!\` and bare \`/-\` at depth 0 (all three open a
nested block comment in Lean 4), verified against a synthetic file with \`sorry\` in
each comment form, and the real sorry register is unchanged at 12.

### R-30 two faithfulness bugs found by review after sign-off, and the pattern behind them

An external reviewer compared the port against the current Rust and found a real
divergence in the Fiat-Shamir schedule. I confirmed it against the source and fixed
it; while reviewing the fix I found a second bug of the same family in code I had
landed earlier the same session.

* **Phase interleaving.** `verifier.rs:108-144` nests the loops with *phase* as the
  outermost axis: for each phase, all proofs' columns of that phase, then that
  phase's challenges. `parseTrace` read every advice commitment and then squeezed
  every challenge. The two agree only for a single phase, or a single proof with no
  challenges - which is exactly the supported profile, so no theorem depends on it
  and no KAT caught it. For a multi-phase key it is a different transcript, i.e. a
  different language accepted.
* **A `foldlM` that ignored its accumulator.** In `partiallyEvaluateIdentities` the
  step returned one proof's terms without appending, so the fold silently became
  "last one wins". Again invisible at `numProofs = 1`.

The pattern is worth naming, because it generalises R-20: **both bugs were undetectable
by any test on the supported profile.** A KAT built on the smallest well-formed input
cannot distinguish "one" from "all". Where the Rust has a loop over a dimension that
our supported configuration collapses to one - phases, proofs, chunks, columns - a
test needs that dimension to have size at least two, and the port should say so
explicitly. Both new KATs do: `phaseInterleave_kats_ok` uses two phases and two
proofs; `multiProofPartiallyEvaluate_kats_ok` uses two proofs and, pointedly, needs
*every* per-proof vector to have two rows because the progressive zip truncates to
the shortest - which is itself R-3's iterator semantics showing up as a test fixture
requirement.

The reviewer's third finding - commitment deduplication by value where the Rust uses
`std::ptr::eq` - is R-7, already known and deliberate (Lean has no allocation
identity). No change; recorded so the review and the log agree on what is a finding
versus a decision.
### R-31 The review process was one-sided: reviewed code had no bugs, unreviewed code had both

Prompted by a direct question from the user: was every step of the translation
reviewed by a fresh adversarial agent? No. The sign-off table shows a clean split:

* Every package a sub-agent wrote was independently reviewed (by me): Arith/Domain,
  Poly, Circuit \`ec1d19e\`, Permutation/Logup/Trash, Yul/Externals, Spec/Degrees,
  Accumulator, Verifier \`389a0c4\`. Roughly 5,900 lines.
* Every package I wrote was reviewed by nobody: \`reviewer | -\` or
  \`agent (self)\` across Transcript, Bytes, Codec, Query, Kzg/{Utils,MultiOpen,Msm,
  Params}, VerifyingKey, Linearization, Verifier (parse_trace), Pcs - **3,122 lines**.

Both serious bugs that survived to late review are in the second set: R-20 in
\`Common/Bytes.lean\` (marked self-reviewed) and R-30 in \`Exec/Verifier.lean\`
(marked \`-\`). The sign-off row for the buggy \`parseTrace\` read "schedule KATs pin
byte accounting" - true, and about the wrong property.

Two structural causes, both fixable:

1. **No agent was ever tasked with attacking a module.** Every cross-check that found
   something (R-20, R-22, R-25, R-27) was incidental - an agent porting a *different*
   module against an independent source of truth. Valuable, but luck-shaped: it only
   catches what overlaps with whatever else is being ported. I wrote in R-20 that
   cross-module porting "should be scheduled as a review mechanism rather than left to
   parallelism" and then did not schedule it.
2. **R11 as written is satisfiable by the author.** "Signed off by a second agent" is
   technically satisfied when a different agent signs off - so it protected the
   sub-agents' work and not mine. Proposed amendment, needing sign-off since the plan
   is normative: *a sign-off is void if the reviewer is the author of the change*, and
   every port PR names the independent reviewer.

Concrete response, not just a concession: the next free sub-agent slot is an
**adversarial review** of the 3,122 unreviewed lines, briefed to assume a divergence
exists and to hunt for the specific failure shapes we have already been bitten by -
flattened loop nesting, iterator semantics paraphrased rather than mirrored, folds
that ignore their accumulator, direct indexes that default instead of faulting,
endianness asserted rather than pinned, and comments that describe the Rust while the
code does something else. Reviewers are told to report only what they verified, with
both citations, and to separate confirmed divergence from suspicious-but-unsettled.

Process note for future rounds: when a module is authored by whoever is coordinating,
it is exactly the module that will not get reviewed. Budget review slots explicitly
rather than letting authorship capacity absorb them.

### R-32 rule R8 violation: the committed-instances feature was normalised in only one of the two places

Second external audit. Of its four findings, two were already logged (R-7 pointer-vs-
value commitment equality; R-27 the frozen §9.2 arity) and one is a documented scope
exclusion (plan Section 1 puts transcripts other than Keccak out of scope, so the
Lean port being Keccak-only is intended). The remaining one is a real bug and it was
mine to miss.

`verifier.rs` shadows the caller's `committed_instances` with `vec![vec![];
instances.len()]` under `cfg(not(feature = "committed-instances"))` in TWO places -
`parse_trace` at :46-47 and `verify_algebraic_constraints` at :260-261 - and in
`parse_trace` the shadow happens **before** the `is_empty` check at :49. The port
normalised only inside `verifyAlgebraicConstraints`, so with the feature off:

* an empty committed argument was rejected as `InvalidInstances` where the Rust
  accepts it (the synthesised rows are non-empty whenever there is a proof), and
* a non-empty committed argument was absorbed into the transcript where the Rust
  would never have seen it - a **different challenge stream**, i.e. a different
  language accepted, not merely a different error.

Rule R8 says every `#[cfg(feature)]` becomes an `if F.x then ... else ...` and both
branches are ported. The feature was ported once instead of twice, which is exactly
the kind of thing a line-range checklist passes: both sites cite the same Rust
construct, so one looks like coverage of the pair.

`committedInstancesOff_kats_ok` pins four separately probed facts: feature off with
an empty argument is accepted; feature off ignores a non-empty argument entirely
(identical outcome to the empty case); feature on still rejects an empty argument;
and a discriminator where one committed plus one normal instance column is legal
only with the feature on. The first draft of that KAT had a conjunct that was
vacuously true - the case I picked was rejected by the shape check for an unrelated
reason - so each conjunct is now evaluated on its own, which is how the problem was
caught.

**On the audit's proposal to model allocation identity explicitly** (a token on
`CommitmentReference::OnePiece`, same token for reuses of one Rust commitment,
different tokens for equal-valued distinct allocations, and not via
`CommitmentLabel`): it is the right fix if we ever want the feature-off or
duplicate-commitment behaviour to match Rust exactly, and it is cheap. But it is a
design decision, not a mechanical one - it changes what `constructIntermediateSets`
takes as input, and under `Features.solidity` the divergence is unreachable for
honest proofs because every commitment is read once from the transcript into its own
slot. Recorded as an option under R-7 rather than implemented. Owner: whoever
settles R-7.
### R-33 The Lean verifier now EXECUTES end to end and discriminates valid from invalid

The most consequential thing to land in this project so far, and the first time any of
it has run. `Midfall/Instances/ExponentModel.lean` (578 lines) supplies a model of
`AdmissiblePairing` by representing each group as its **exponent lattice**:
`Exp p := Multiplicative (ZMod p)`, pairing = multiplication of exponents, generators
= exponent 1. Bilinearity holds by construction, `e g₁ g₂ ≠ 0` holds, `DecidableEq` is
available, and `DualMSM.check` becomes a decidable linear equation over `ZMod p`.

I verified the headline claim independently rather than trusting the report:

    accepted pi in 0..16 = [11]        -- exactly one accepted
    every pi runs to completion, consuming exactly 304 bytes

So `Verifier.prepare` - `parseTrace` → `verifyAlgebraicConstraints` →
`partiallyEvaluateIdentities` → `computeLinearizationCommitment` → `multiPrepare` →
`DualMSM` - executes on a hand-built proof and the final equation separates the one
valid π from sixteen invalid ones. Both channels are non-identity points and the
right channel is a 7-term sum that genuinely cancels, so this is not a degenerate
fixture passing by accident.

**What this does and does not certify.** It shows the `AdmissiblePairing` hypotheses
are *satisfiable* - D-P1's abstraction is not vacuous - and it makes the Exec code
runnable. It is a model of exponent arithmetic, NOT of BLS12-381: every element is
its own discrete log, so it can say nothing about DL hardness, binding, or the
subgroup checks G1ADD omits. The real curve instance is still owed by
`Assumptions/Pairing.lean`, and no theorem depends on this file (the dependency runs
one way, Instances → Exec). Plan Section 5 explicitly sanctions the strategy: "if
the pairing is not executable in Lean, it compares the pairing inputs and the Rust
check result" - this is that fallback, made concrete.

**Two harness-relevant facts it discovered**, both of which the conformance exporter
will have to respect: a gate containing `Expression.selector` panics at mod.rs:532
(virtual selectors are gone by VK time, so an exported CS must use `Expression.fixed`
with a simple-selector flag), and every field element read from a proof must be
canonical, so a naive all-`0x01` buffer fails as a transcript error - rule R7
working, not a bug.

**A correction to my own brief, again (see R-29).** I told the agent to build the
carrier as `Additive (ZMod p)`. That can never carry a `Group`: mathlib's `Additive`
only transfers multiplicative structure *into* additive structure
(`TypeTags/Basic.lean:16-19`), so the tag for "`ZMod p` with its addition as a
multiplicative group" is `Multiplicative`. My probe had failed on exactly this and I
passed the failure on as an instruction. Two rounds in a row that my briefs were the
weakest link; they need to be treated as code.

Three class improvements it reported rather than making (the class is boundary-frozen):
`MSMKZG.check` needs only `decEqG₁` but must pin `G₂`/`Gₜ` at every call site, which a
one-group decidable class would fix; there is no field saying the generators are
*bases* (`∀ x, ∃ s, gsmul s g₁ = x`), which is precisely the assumption the exponent
model satisfies by construction and the harness leans on implicitly; and no
`DecidableEq G₂`. Owner: `Common/Curve.lean`, low urgency, but the second one should
be stated before the conformance soundness argument is written down.
### R-34 The blst differential review: five codec defects and a gate that could not fail

An adversarial review compiled **blst 0.3.17 against the repo's own `libblst.a`** —
the exact code `g1.rs:369-372` delegates to — and differential-tested the Lean G1
codec over 66 targeted plus 1,784 randomised inputs, diffing verdicts *and* decoded
coordinates. Five defects, four of them in code I had committed within the previous
two hours, including one that re-opened a bug I had declared fixed.

* **Infinity arm was not canonical** (fixed `8ba4f05`). blst requires the sort bit
  *and* the low six bits of byte 0 to be zero (`e1.c:269-274`), not just bytes 1..47.
  So `e0`, `c1`, `ff`, `df`, `f0` each followed by 47 zeros all decoded to the
  identity — same absorbed bytes, same challenges, same decision. The KAT written to
  catch this put the dirty byte in **byte 1**, which both sides already rejected, so
  it passed while the hole was open.
* **`x = 0` was accepted** (fixed `8ba4f05`). Gives `(0, ±2)`, the order-3 points —
  the textbook small-subgroup input. blst rejects them inside `blst_p1_uncompress`
  (`e1.c:288-289`) *before* any torsion test, so the file's "torsion needs the group
  law, out of scope" disclaimer did not cover it: this is a zero test.
* **The sign-convention KATs were vacuous** (fixed `8ba4f05`). Decode-with-C then
  recompress-with-C is the identity for *any* C; the reviewer proved it by swapping
  largest-root for odd-root and watching all six KATs stay green. Replaced with a
  KAT anchored to the **published generator**, whose `y` is the smallest root and is
  odd while the largest root is even — the conventions disagree on it. Verified
  non-vacuous by execution. The convention itself was independently confirmed correct
  via `e1.c:208` and 21/21 agreement with blst on the real trace points.
* **`ofEip?` ignored the two 16-byte pads** (fixed `447e4d4`), so the 128-byte form
  was non-injective — the same malleability class as the two items above.
* **`eipRoundtrip` was stated in the wrong direction** (fixed `447e4d4`).
  `∀ P, ofEip? (toEip P) = some P` is false for any representation with redundant
  structure: `⟨isInfinity := false, x := 0, y := 0⟩` is not a point, yet `toEip`
  maps it to 128 zeros and the decoder correctly returns the identity. Restated
  decoder-first, `∀ b P, ofEip? b = some P → toEip P = b`, mirroring
  `compressedRoundtrip`, which was already stated that way.

Two documentation obligations surfaced here, still open: no Lean instance can satisfy
plan 9.1's `ofEip? = (E1.ofEip? b).bind toSubgroup?` because the torsion test needs
the group law, and **no Rust code ever decodes the 128-byte form** —
`implementors.rs:283-299` is `to_input`, a writer; the reader is the 48-byte path at
`:304-311`. So `ofEip?` is a Lean-side definition serving the contract model and
must not be cited as a port.

**The meta-finding, and the one to keep.** The review also proved that
`kat_gate.py` — written an hour earlier to stop KATs from silently not running —
itself had two ways to report success while a check was broken: an annotation with
trailing prose (`-- expect true, and checks.sh asserts it`) parsed as *unannotated*
and was skipped, which left `pBaseKats_ok`, the modulus guard, ungated; and the
subprocess exit status was ignored, so a KAT file that did not compile could pass.
Both fixed in `7a059b4`, then `3481f9b` annotated the 32 remaining bare `#eval`s.
**112 checks now gate CI, up from 70, with zero unannotated lines.** The lesson is
not "use blst" — it is that a gate needs its own falsification test, and that
reporting "N checks pass" as a success metric hides "M checks were never looked at".

Also found and fixed: **HEAD did not build** (`bfbfbe2`). The D-P9 re-pin existed
only as uncommitted working-tree edits, so every commit since `972c6b2` was red on a
fresh checkout while looking green locally — and the commit message claimed the
re-pin had landed. Waiting for permission to commit someone else's decided change was
the wrong call when HEAD was broken.

### R-35 R-2's second face is reachable from a proof byte, demonstrated end to end

`docs/REVIEW.md` R-2 recorded three manifestations of the "squeezed challenge lands
on a bad point" hazard, the second being `poly/kzg/mod.rs:479` —
`den.invert().unwrap()` in the multi-open `v` computation. It was documented from
reading the Rust, with no demonstration that a real proof could provoke it.

`Instances/NativeE2E.lean` KAT 14 now demonstrates it. Setting the
**committed-instance evaluation byte to 13** makes the squeezed `x3` coincide with a
point of the open set, the denominator vanishes, and `verifyNative` propagates
`Fault.panic "proofs/src/poly/kzg/mod.rs:479"` rather than collapsing it to
`Error::Opening`. The other sixteen values at the same `pi` all run to completion
(two accept, fourteen reject with opening), so the panic is a property of that input,
not of the fixture.

Why it matters: the panic is reachable from a byte the prover controls, in the path
that runs after the transcript is fully consumed. The reference aborts there, so the
port is faithful — but any statement of the form "the verifier rejects bad proofs
with `Error::Opening`" is false as written, and a caller treating a panic as an
infrastructure error rather than a rejection would diverge between Lean and Rust.
The port keeps the distinction (rule R4) precisely so this stays visible.

Also from the same package, for the conformance harness: a truncated proof faults
`Error::Opening`, **not** a transcript error, whenever the short read lands inside
`multiPrepare` — the deliberate collapse at `Exec/Verifier.lean:948-949`. So a test
phrased as "rejects a mutated proof with opening" passes vacuously on a truncated
proof. Every rejection KAT in `NativeE2E` names its fault for that reason.

Finally: the plan's `[[0]]` committed-instance placeholder was checked against the
baseline Rust and `[[1]]` is correct — the identity-accumulator case passes
`&[&committed_pi]` with one committed column holding the identity plus one public
column, which is what forces `numInstanceColumns = 2`. In the exponent model `0`
does not even typecheck at `List (List G₁)` for an abstract `Group`.
## Closed

- `msm_inner_product` was deferred by the Arith/Domain package as
  verifier-reachable but MSMKZG-typed; it is now `msmInnerProduct` in
  Exec/Kzg/Msm.lean, with the `zip` truncation hazard documented (a dropped
  MSM is dropped *un-scaled*, not scaled-and-ignored).
- `trait MSM` is deliberately not a structure of functions; the reason is in
  Exec/Kzg/Msm.lean.


### R-7 pointer equality in CommitmentReference - must be settled, not assumed

`impl PartialEq for CommitmentReference` compares OnePiece with
`std::ptr::eq` (query.rs:125), i.e. *address* identity, and compares Linear by
points and scalars while explicitly ignoring the labels (query.rs:129). An
owned-value port cannot reproduce address identity, so `CommitmentReference.beq`
is value equality - a strictly coarser relation. If
`construct_intermediate_sets` uses that comparison to group queries that share
a commitment, then the Rust groups by allocation and the port groups by value:
given two distinct allocations holding the same point, the point sets differ
and the challenge structure (x1, x2, x3) differs with them. Either the Rust is
relying on value equality and the pointer compare is an optimisation, or it is
not. Decide when that function is ported and record it here; the conformance
corpus should contain a query set with a repeated commitment so the answer is
empirical rather than argued.
  **Scope widened by Exec/Poly:** the same pointer identity also decides whether
  `Error::DuplicatedQuery` fires at all (utils.rs:55-58 tests membership of the
  same commitment), so R-7 is not only about grouping - it is on the error path
  too, and a query set with two allocations holding one point changes the
  accept/reject decision, not just the point-set layout. Exec/Kzg/MultiOpen
  instantiates the relation with `kzgCommitBeq` (value equality, labels ignored
  exactly as the Rust does); the corpus case is still owed.

## Next work packages

1. ~~`Exec/Poly`~~ done (`451a491`): only `poly::Error` and `Rotation` are
   verifier-reachable; `Polynomial` is prover code and is NOT part of L0.
   ~~`multi_prepare` + `construct_intermediate_sets`~~ done (`363d2cd`, `8df0e05`).
   Remaining before `Exec/Verifier`: `Exec/Pcs` (`poly/commitment.rs` - the
   `PolynomialCommitmentScheme` and `Guard` records per R9) and `Exec/Kzg/Utils`
   is done, so next is `Exec/VerifyingKey` (where R-1 lives) and then
   `Exec/Verifier` (where R-8 lives).
2. `Exec/VerifyingKey`: the real `VerifyingKey` record, `hash_into`, and the
   `transcript_repr` decision (R-1).
3. `Exec/Permutation`, `Exec/Logup`, `Exec/Trash`, `Exec/Linearization`:
   verifier paths only.
4. `Exec/Verifier`: `prepare`, then `Exec/Native` loses its four sorries.
5. `Assumptions/Pairing.lean`: the named BLS12-381 hypothesis, including
   `G1Codec`, `FieldConsts` and the R-3 properties.

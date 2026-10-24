# Port review log (plan rule R11)

Rule R11: every module PR carries a checklist mapping Rust line ranges to
Lean defs, signed off by a second agent. The checklists live in the commit
bodies; this file records *who reviewed what*, and - more usefully - every
finding that needs an owner outside the module that surfaced it.

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

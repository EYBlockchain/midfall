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
| `msmInnerProduct` closes the deferred item | `a8cf7f2` | agent | - | - |

The Arith/Domain review spot-checked the two claims most likely to be wrong
against the Rust: `g_coset_inv = g_coset.square()` (domain.rs:82 - correct,
and only an inverse because zeta^3 = 1) and the chained `batch_invert` order
(domain.rs:117-124 - t_evaluations, ifft_divisor, extended_ifft_divisor,
barycentric_weight, extended_omega_inv, omega_inv; correct).

## Findings that need an owner outside their module

### R-1 `transcript_repr` needs byte-exact Rust `{:?}` output - UNOWNED

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

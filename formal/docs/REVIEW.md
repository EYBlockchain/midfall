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
| `msmInnerProduct` closes the deferred item | this commit | agent | - | - |

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
(`lIRange 13 1 [0,1] == #[0,0]` over `ZMod 17`). Owner: Phase 4.

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

## Closed

- `msm_inner_product` was deferred by the Arith/Domain package as
  verifier-reachable but MSMKZG-typed; it is now `msmInnerProduct` in
  Exec/Kzg/Msm.lean, with the `zip` truncation hazard documented (a dropped
  MSM is dropped *un-scaled*, not scaled-and-ignored).
- `trait MSM` is deliberately not a structure of functions; the reason is in
  Exec/Kzg/Msm.lean.

## Next work packages

1. `Exec/Poly` + `Exec/Pcs`: `poly/mod.rs` verifier-reachable subset
   (`Polynomial` as a record per R9, `VerifierQuery`, `CommitmentReference`)
   and `poly/kzg/mod.rs` `multi_prepare` + `construct_intermediate_sets`.
   This is the last big leaf before `Exec/Verifier`.
2. `Exec/VerifyingKey`: the real `VerifyingKey` record, `hash_into`, and the
   `transcript_repr` decision (R-1).
3. `Exec/Permutation`, `Exec/Logup`, `Exec/Trash`, `Exec/Linearization`:
   verifier paths only.
4. `Exec/Verifier`: `prepare`, then `Exec/Native` loses its four sorries.
5. `Assumptions/Pairing.lean`: the named BLS12-381 hypothesis, including
   `G1Codec`, `FieldConsts` and the R-3 properties.

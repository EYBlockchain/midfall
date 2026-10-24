-- |
-- Midfall.Halo2.Exec.Poly
--
-- Faithful port of the verifier-reachable subset of `proofs/src/poly/mod.rs`
-- (526 lines) (plan Section 4 module map, row
-- `poly/{mod,domain,query,commitment}.rs -> Exec/{Poly,Domain,Query,Pcs}`).
--
-- THE HEADLINE IS A REACHABILITY RESULT, NOT A BODY OF CODE. `poly/mod.rs` is
-- the *prover's* univariate-polynomial layer. The verifier's data plane is
-- commitments and evaluations (`VerifierQuery`, Exec/Query) plus the MSM
-- accumulators (Exec/Kzg/Msm): it never holds a coefficient vector, a Lagrange
-- vector or a coset vector. Grepping the verifier-reachable set
-- (plonk/verifier.rs, plonk/{permutation,logup,trash,linearization}/verifier.rs,
-- plonk/mod.rs, poly/kzg/, poly/{query,domain,commitment}.rs and
-- proofs/solidity-verifier/src) for `Polynomial` returns hits in exactly six
-- places, and every one of them is prover-side:
--
--   plonk/mod.rs:339-344        the `ProvingKey` fields
--   poly/kzg/mod.rs:159,:168    `commit` / `commit_lagrange` (PCS prover ops)
--   poly/kzg/mod.rs:190-192,    `poly_inner_product` and the two
--                   :273,:311   `Polynomial { .. }` literals, all inside
--                               `multi_open` (kzg/mod.rs:177-319)
--   poly/query.rs:56,:64,:72    `ProverQuery` / `PolynomialPointer`
--   poly/domain.rs:147-336      the FFT transport and the domain constructors
--   poly/commitment.rs:44,:50   the two prover methods of the PCS trait
--
-- No verifier-reachable function has a `Polynomial` in its signature or its
-- body, so none of the `impl` blocks over it - including the operator impls,
-- which only ever apply to `Polynomial` values - can be reached. Of the 526
-- lines, two items are reachable:
--
--   * `enum Error` (33-44), ported below as `PolyError`;
--   * `struct Rotation` and `cur`/`prev`/`next` (505-526), already ported in
--     Exec/Circuit (the type) and Exec/Domain (`Rotation.int`).
--
-- Everything else is a documented skip, in source order, with the grep evidence
-- at each site.
--
-- Port rules applied: R1 provenance on every def *and* on every skip; R2 names,
-- with one forced deviation explained at `PolyError`; R3 iterator semantics (no
-- reachable item iterates); R4 panics become
-- `.error (Fault.panic "<path>:<line>")` - no reachable panic site exists in
-- this file, and the ones the skips hide are recorded at each site; R5
-- `Nat`/`Int` with no wrapping emulation; R6 `Vec` -> `Array`; R7; R9 traits ->
-- records of functions; R10 computable, never `partial`, no proofs in Exec.
--
-- Not here by the plan's own division of labour: `Expression::evaluate` lives
-- in plonk/circuit.rs and belongs to Exec/Circuit; `VerifierQuery` and
-- `CommitmentReference` live in poly/query.rs and are in Exec/Query; the PCS
-- trait in poly/commitment.rs is Exec/Pcs.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

/-- rust: proofs/src/poly/mod.rs:33-44 (`pub enum Error`), i.e. `crate::poly::Error`.
    The only reachable item declared in this file.

    R2 DEVIATION, recorded because it is a name change: the Rust type is `Error`
    and the port calls it `PolyError`. Rust distinguishes it from
    `crate::plonk::Error` (Exec/Error.lean, already `Midfall.Halo2.Error`) only
    by module path, and the Lean port keeps the flat `Midfall.Halo2` namespace
    that Exec/Domain and Exec/Query established for the `poly` modules - so the
    module has to move into the name. `crate::poly::Error` -> `PolyError` is the
    reading to use when checking provenance.

    The Rust derives only `Debug` (mod.rs:35) - no `Clone`, no `PartialEq` - so
    nothing in Rust ever compares these; they are produced, propagated with `?`
    and consumed. The port matches that and carries *no* equality instance, so a
    downstream `match` can inspect a `PolyError` but cannot test one for
    equality; the KATs at the bottom of this file tag the variants instead. The
    source carries its own warning at mod.rs:34:
    `// TODO: these errors need to be cleaned up`.

    WHERE THE VARIANTS ARE ACTUALLY OBSERVABLE - read this before mapping them.

    * `openingError` (mod.rs:37-38, "OpeningProof is not well-formed"): built at
      poly/kzg/msm.rs:232, `<DualMSM as Guard>::verify` - the final pairing
      check failed. That is the *two-phase* API, and there the error does reach
      the caller: proofs/solidity-verifier/src/test.rs:370-380 is exactly
      `prepare(..)` followed by `guard.verify(&params.verifier_params())`.
      The other four sites (poly/kzg/mod.rs:213, :283, :292, :318) are inside
      `multi_open`, i.e. the prover.
    * `samplingError` (mod.rs:39-40, "Caller needs to re-sample a point"): built
      at poly/kzg/mod.rs:341, :447, :463 and :534, every one of them
      `transcript.read().map_err(|_| Error::SamplingError)` inside
      `multi_prepare`. :341 is under `cfg(feature = "fewer-point-sets")`, which
      is `Features.outerFewerPointSets` (rule R8; BASELINE.md records it as
      *false* in the production profile), so the reachable ones are :447 (the
      `f_com` read), :463 (the `q_eval` reads, one per point set) and :534 (the
      `pi` read).
    * `duplicatedQuery` (mod.rs:41-43, "Multiopen argument only supports a
      single query to the same (commitment, opening) pair"): built at
      poly/kzg/utils.rs:58 in `construct_intermediate_sets`, reached from
      `multi_prepare` at poly/kzg/mod.rs:371. Note the dependency on
      docs/REVIEW.md R-7: "the same commitment" is `PartialEq` on
      `CommitmentReference`, whose `OnePiece` arm is `std::ptr::eq`
      (poly/query.rs:125), so *whether this error fires at all* is a question
      about allocations, not about values.

    THE ERASURE, and it is not uniform. At the single verifier-reachable call
    site of `multi_prepare` the whole enum is dropped:
    `CS::multi_prepare(&queries, transcript).map_err(|_| Error::Opening)`
    (plonk/verifier.rs:651) - every `poly::Error` becomes `plonk::Error::Opening`.
    But the reads `multi_prepare` does *itself* are relabelled `SamplingError`
    from an `io::Error`, which discards the `io::ErrorKind`, while the reads the
    plonk verifier does directly (plonk/verifier.rs:118, :358) go through
    `impl From<io::Error> for plonk::Error` (plonk/error.rs:44-49) and become
    `Error::Transcript(io)`. So the *same physical failure* - a proof stream that
    runs out of bytes - produces `Error::Transcript(UnexpectedEof)` when the
    plonk verifier is the reader and `Error::Opening` when the PCS is. Which
    module reads a given field is therefore observable in the error class, and
    the port must keep that split rather than normalise it.
    Exec/Kzg/Msm.lean:245 and Exec/Kzg/Utils.lean:119-122 currently encode every
    `poly::Error` as `Fault.error Error.opening`; that is faithful at the
    `verify_algebraic_constraints` boundary and lossy at the `prepare` /
    `Guard::verify` boundary that Exec/Native ports. Owner of the decision:
    Exec/Verifier and Exec/Native. -/
inductive PolyError where
  /-- rust: poly/mod.rs:37-38 `OpeningError` -/
  | openingError
  /-- rust: poly/mod.rs:39-40 `SamplingError` -/
  | samplingError
  /-- rust: poly/mod.rs:41-43 `DuplicatedQuery` -/
  | duplicatedQuery

/-! rust: proofs/src/poly/mod.rs:20-29 (`mod domain; mod query; pub mod kzg;
    pub mod commitment;` and the two `pub use` lines) - module structure, not
    items, so nothing to port. The mapping is the plan's Section 4 module map:
    domain.rs -> Exec/Domain, query.rs -> Exec/Query, kzg/ -> Exec/Kzg/*,
    commitment.rs -> Exec/Pcs. `pub use query::{CommitmentLabel, VerifierQuery}`
    at :29 is why those two are spelled `crate::poly::CommitmentLabel` at their
    use sites although they live in query.rs; `pub use domain::*` at :28 is the
    same for `EvaluationDomain` and `Rotation`. `ProverQuery` is imported by :29
    too and is not ported (prover, plan Section 1). -/

/-! rust: proofs/src/poly/mod.rs:47-80 (`trait PolynomialRepresentation`: `len`,
    `empty`, `omega`, `k`, `coeff_to_self`, `g_coset`) and :82-165 (the three
    impls, for `Coeff`, `LagrangeCoeff` and `ExtendedLagrangeCoeff`) - NOT
    verifier-reachable, so no bodies.

    Evidence: outside poly/mod.rs the trait name occurs only at
    plonk/evaluation.rs:7 (import), :52, :113, :361, :807, :856 and
    plonk/prover.rs:29 (`AdviceSingle<F, B: PolynomialRepresentation>`).
    `plonk/evaluation.rs` is the prover's evaluation engine: its entry points
    are `Evaluator::evaluate_numerator` (evaluation.rs:361), called from
    plonk/prover.rs:772, and `Evaluator` itself is a `ProvingKey` field
    (plonk/mod.rs:346, built at :427 and keygen.rs:345). `coeff_to_self` is
    called only at evaluation.rs:440, :526, :528, :529, :597, all inside
    `evaluate_numerator`. `g_coset::` has zero call sites anywhere in the crate.
    The three marker types are imported by plonk/mod.rs:14 but used only in the
    `ProvingKey` fields (:339-344).

    Recorded for whoever ports the prover, because the three impls are *not* the
    same shape: `len` is `domain.n` for `Coeff` and `LagrangeCoeff` but
    `domain.extended_len()` for `ExtendedLagrangeCoeff` (:144); `omega` is
    `get_omega` for the first two and `get_extended_omega` for the third (:148);
    `g_coset` is `F::ONE` for the first two and `domain.g_coset` for the third
    (:163) - only the extended representation lives on a coset, which is what
    makes the quotient argument work. `empty` (:54-61) is a *default* method,
    `vec![F::ZERO; Self::len(domain)]`, so the length of a zero polynomial is
    representation-dependent. Under rule R9 the trait becomes a record of six
    functions over `EvaluationDomain`; the markers themselves carry no data
    (`PhantomData`, :172), so in Lean they are `Unit`-like tags. -/

/-! rust: proofs/src/poly/mod.rs:167-173 (`struct Polynomial<F, B> { values:
    Vec<F>, _marker: PhantomData<B> }`) and :175-183 (`init`) - NOT
    verifier-reachable; no body. The reachability argument is the one in this
    file's header: the type occurs only in `ProvingKey` (plonk/mod.rs:339-344),
    the PCS prover methods (poly/kzg/mod.rs:159, :168, :190-192, :273, :311),
    `ProverQuery`/`PolynomialPointer` (poly/query.rs:56, :64, :72), the domain
    constructors and FFT transport (poly/domain.rs:147-336) and the PCS trait
    (poly/commitment.rs:44, :50).

    Notes for the prover port, none of which change a verifier result.
    `_marker` is `PhantomData` and carries no data, so rule R6 renders the struct
    as `{ values : Array F }` with the representation as a type parameter - that
    is what the plan's "`Polynomial` as a record per R9" means.
    `#[derive(Eq, PartialEq)]` at :169 compares `values` *including length and
    trailing zeros*, so two coefficient vectors differing only by a trailing zero
    are unequal as `Polynomial`s - unlike the polynomial they denote. `init`
    (:177-182) has exactly one call site in the crate,
    plonk/linearization/prover.rs:52. `Coeff` derives `Eq, PartialEq` (:83) while
    `LagrangeCoeff` and `ExtendedLagrangeCoeff` derive only `Clone, Copy, Debug`
    (:111, :140) - an asymmetry with no consequence, since the markers hold no
    data. -/

/-! rust: proofs/src/poly/mod.rs:185-228 (`padded_add`, `padded_sub`) - NOT
    verifier-reachable; no bodies. `padded_add` is called once, at
    poly/kzg/mod.rs:197 inside `poly_inner_product`, a nested function of
    `multi_open` (poly/kzg/mod.rs:177-319) - the prover. `padded_sub` is called
    once, at plonk/linearization/prover.rs:82.

    Two things worth recording, because both are the kind of thing a tidy port
    would silently change. (1) The length semantics are *not* symmetric: the
    shorter side is zero-extended by `resize` (:196, :218) and the longer side is
    never truncated, so the result length is `max(len lhs, len rhs)` - and
    `padded_add` exists precisely because `Add` *asserts* equal lengths (:401,
    :420) where these do not. (2) The `parallelize` closure at :198-204 guards
    with `rhs.values.get(start..)` and skips the chunk entirely when that returns
    `None`. After the `resize` that cannot happen for the vector as a whole, but
    it is a silent degradation if the resize is ever removed - and `parallelize`
    is a rayon work splitter whose chunk boundaries depend on the machine (see
    the Exec/Arith:169-178 skip note on `parallelize`). -/

/-! rust: proofs/src/poly/mod.rs:231-285 (`Index<usize>`, `IndexMut<usize>`,
    `Index<RangeFrom<usize>>`, `IndexMut<RangeFrom<usize>>`, `Index<RangeFull>`,
    `IndexMut<RangeFull>`, `Deref`, `DerefMut`) - NOT verifier-reachable; no
    bodies. They are impls on `Polynomial`, which the verifier never has (header
    argument).

    R4 note for the prover port: all six indexing impls delegate to `Vec`/slice
    indexing, so every one of them is an out-of-bounds panic site (:235, :241,
    :249, :255, :263, :269) and would become `Fault.panic`. `Deref` to `[F]`
    (:276-278) is what makes `&poly[..]` compile, which is how
    `eval_polynomial(&poly[..], x)` is written in the prover and in the domain
    tests (poly/domain.rs:530). -/

/-! rust: proofs/src/poly/mod.rs:287-305 (`iter`, `iter_mut`, `num_coeffs`) - NOT
    verifier-reachable; no bodies. `iter` is used by `batch_invert_rational`
    (poly/mod.rs:338, :344) and by the prover; `iter_mut` occurs at
    poly/domain.rs:513, which is inside `mod tests` (domain.rs:501 `#[test]`,
    :502 `fn test_rotate`).

    `num_coeffs` (:302-304) has **zero call sites anywhere in the crate**:
    `grep -rn num_coeffs proofs/src` returns the definition and nothing else.
    Dead code in the reference, so porting it would add a Lean def that no
    conformance trace can ever exercise. Recorded rather than ported. -/

/-! rust: proofs/src/poly/mod.rs:307-331 (`read`, `write`) - NOT
    verifier-reachable; no bodies. `Polynomial::read` is called only from
    `read_polynomial_vec` (utils/helpers.rs:141), whose callers are
    `ProvingKey::read` (plonk/mod.rs:416) and `permutation::ProvingKey::read`
    (plonk/permutation.rs:154); `Polynomial::write` only from
    `write_polynomial_slice` (helpers.rs:146-155, call at :152), called from `ProvingKey::write`
    (plonk/mod.rs:384) and `permutation::ProvingKey::write`
    (plonk/permutation.rs:166). All of it is the *proving* key codec: the
    verifying key codec (plonk/mod.rs:94-215) never touches a polynomial, which
    is why the VK reader works over commitments only. This is the same plumbing
    Exec/Arith:382-394 declines for `read_polynomial_vec`.

    Two hazards recorded for the PK codec work package. (1) `write` at :325 is
    `(self.values.len() as u32).to_be_bytes()`: a `usize as u32` **cast**, which
    truncates silently in *every* build profile (a cast is not an overflow check),
    so a polynomial with 2^32 or more coefficients writes a length that does not
    describe its body. Unreachable in practice - `k <= F::S` bounds the length -
    but it is a truncation, not a panic, and it is the kind of thing R-6 exists
    for. (2) `read` at :312 takes the length from the stream as a `u32` and then
    loops `0..poly_len` reading field elements, so a corrupt length is an
    unbounded read attempt with no bound check first; the failure surfaces as an
    `io::Error` from `read_f`, i.e. `Error::Transcript` at the plonk boundary,
    not a validation error. -/

/-! rust: proofs/src/poly/mod.rs:333-356 (`batch_invert_rational`) and :358-374
    (`Polynomial::<Rational<F>, LagrangeCoeff>::invert`) - NOT
    verifier-reachable; no bodies. `batch_invert_rational` is called at
    plonk/prover.rs:676 and plonk/keygen.rs:274 and :329 - the prover and keygen,
    both out of scope by plan Section 1. `invert` has exactly one caller,
    `batch_invert_rational` itself at :354.

    Recorded because this is the one place in the file where a zero is *silently*
    turned into a one: `Rational::denominator()` yields `Option<F>`,
    `filter_map(|d| d.as_mut())` (:347) drops the trivial ones from the batch,
    and `d.unwrap_or(F::ONE)` (:354) puts a 1 back in their place - so a rational
    with a trivial denominator passes through as `numerator * 1`. That is correct
    arithmetic, but it also means a malformed rational whose denominator happened
    to be `ONE` is indistinguishable from one that was skipped. `invert` carries
    a real panic site: `assert_eq!(inv_denoms.len(), self.values.len())` at :363,
    which under R4 would be `Fault.panic "proofs/src/poly/mod.rs:363"`. The `zip`
    at :368 truncates to the shorter input (R3) if that assert is ever removed,
    which is presumably why it is there. -/

/-! rust: proofs/src/poly/mod.rs:376-450 (`Add<&'a Polynomial>`,
    `AddAssign<&'a Polynomial>`, `Add<Polynomial>`, `Sub<&'a Polynomial>`) - NOT
    verifier-reachable; no bodies. Impls on `Polynomial` (header argument);
    concrete prover sites include plonk/trash/prover.rs:59 (`acc *
    trash_challenge + &expression`, i.e. `Mul` then `Add<&_>`) and
    plonk/evaluation.rs:458-629.

    Panic sites recorded under R4: `assert_eq!(self.values.len(),
    rhs.values.len())` at :401 (`AddAssign`), :420 (`Add` by value) and :441
    (`Sub` by ref). All three are *length* assertions and the Rust doc comments
    name the invariant ("both operands must have been created over the same
    domain"). Note the asymmetry a port must not smooth over: `Add` by value
    (:419) duplicates the body of `AddAssign` instead of delegating to it, while
    `Add` by reference (:385) delegates - so the two assert at :420 and :401
    respectively, and a change to one would not reach the other. -/

/-! rust: proofs/src/poly/mod.rs:452-466 (`Polynomial::<F, LagrangeCoeff>::
    rotate`) - NOT verifier-reachable; no body. Its only call sites are
    poly/domain.rs:517, :518, :519, inside `fn test_rotate` (domain.rs:502) - a
    unit test. The verifier rotates *points* (`EvaluationDomain::rotate_omega`,
    Exec/Domain) and never a value vector.

    Recorded because `rotate` is a minefield, and because it is the one place in
    this file where the reference build profile matters (BASELINE.md: release).
    * `values.rotate_left(rotation.0 as usize)` (:459) and
      `values.rotate_right((-rotation.0) as usize)` (:457): `slice::rotate_left`
      and `slice::rotate_right` **panic when the amount exceeds the length**, so
      a rotation with `|r| > n` panics rather than wrapping. Nothing bounds `r`:
      `Rotation` is a bare `i32` and plonk/permutation/verifier.rs:152 builds
      `Rotation(-((blinding_factors + 1) as i32))` from caller-controlled
      blinding factors.
    * `-rotation.0` at :457 is an `i32` negation, which overflows at `i32::MIN`:
      *panics in debug, wraps in release* - so the reference profile gives
      `i32::MIN` again, `as usize` sign-extends it to `2^64 - 2^31`, and
      `rotate_right` of more than the length panics anyway. Same class as
      docs/REVIEW.md R-5's `i32::abs` note, and the reason a Lean `Int` port must
      not "simplify" that negation.
    * `self.values.clone()` at :455 makes rotation an `O(n)` copy rather than an
      index rotation - irrelevant to meaning, relevant to any gas model. -/

/-! rust: proofs/src/poly/mod.rs:468-503 (`Mul<F>`, `MulAssign<F>`,
    `Sub<F> for &Polynomial`) - NOT verifier-reachable; no bodies. Impls on
    `Polynomial` (header argument); `Mul` is used at poly/kzg/mod.rs:196
    (`p.clone() * s`, inside `multi_open`'s `poly_inner_product`).

    `mul_assign` (:477-493) is worth a note because it is *not* a plain pointwise
    multiply: it special-cases `rhs == ZERO` (write zeros, :479-485) and skips the
    work entirely when `rhs == ONE` (:485). The skip is a performance no-op over a
    field, but it means the observable behaviour on a ring with zero divisors
    would differ from `map(|x| x * rhs)`; under D-P1 the field is `Fr p` with `p`
    prime, so the two agree. `Sub<F> for &Polynomial` (:495-503) subtracts the
    scalar from `values[0]` *only* - an out-of-bounds panic on an empty
    polynomial (:500), and the reason the prover's `l_0`-style "subtract the
    constant term" logic depends on the vector being non-empty. -/

/-! rust: proofs/src/poly/mod.rs:505-526 (`pub struct Rotation(pub i32)` and
    `Rotation::cur`/`prev`/`next`) - REACHABLE, and already ported, so no body
    here. Evidence that it is reachable: plonk/permutation/verifier.rs:151
    (`Rotation::next()`), :152 (`Rotation(-((blinding_factors + 1) as i32))`, the
    raw tuple constructor), plonk/logup/verifier.rs:178 (`Rotation::next()`),
    plonk/mod.rs:510 (`l_i_range` over a `RangeFrom<i32>` of rotations),
    poly/domain.rs:410-418 (`rotate_omega` reads `rotation.0`) and :459, :468,
    and proofs/solidity-verifier/src/builder/mod.rs:15 (the generator imports it).

    Where the port lives: the *type* is `Midfall.Halo2.Rotation`,
    Exec/Circuit.lean:13-15, and the integer the Rust tuple field `.0` carries is
    `Rotation.int`, Exec/Domain.lean:85-94. The three constructors coincide by
    name, which is why nothing new is needed: `Rotation::cur()` is `Rotation.cur`,
    `Rotation::next()` is `Rotation.next`, `Rotation::prev()` is `Rotation.prev`,
    and `Rotation(i)` is `Rotation.value i`.

    THE REPRESENTATIONAL CHOICE, recorded because it is load-bearing for
    Exec/Verifier: Exec/Circuit models `Rotation` as a closed inductive rather
    than as `Int`, which makes it *not* isomorphic to the Rust `i32`.
    (a) `Rotation.cur` and `Rotation.value 0` are two distinct inhabitants in
    Lean and one value in Rust, so a Rust test of `rotation == Rotation::cur()`
    must be ported as `rotation.int == 0`, never as structural equality.
    (b) `Rotation.value` admits every `Int`, including magnitudes outside the
    `i32` range the Rust cannot express, so anything that bounds a rotation by
    `i32::MIN`/`i32::MAX` (see the `rotate` note above, and R-5's `i32::abs`) has
    no Lean counterpart. Both are pinned by the KAT below. -/

/-! ## Known-answer checks

Executable booleans, not proofs, in the style of `Exec/Arith`'s `section Kats`.
There is little arithmetic in the reachable subset of `poly/mod.rs`, so these
pin the two claims this file actually makes: that `PolyError` has three distinct
variants and that the Rust's erasure at plonk/verifier.rs:651 collapses all
three, and that the `Rotation` port (Exec/Circuit + Exec/Domain) agrees with
the Rust `i32` reading on `cur`/`prev`/`next` and identifies `cur` with
`value 0` only through `Rotation.int`. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The `ZMod 17` field constants: `p - 1 = 16 = 2^4`, so `S = 4` and `3` is a
    primitive `2^4`-th root of unity. Same record as Exec/Domain's KAT section;
    re-declared rather than reused because `fc17` there is a test helper, not an
    API. -/
def polyFc17 : FieldConsts (Fr 17) :=
  { numBits := 5, s := 4, rootOfUnity := 3, zeta := 2 }

/-- KAT scaffolding. A numeric tag per `PolyError` variant, so the checks below
    can distinguish them without an equality instance on the type itself (the
    Rust derives only `Debug`, mod.rs:35, so the port deliberately has none).
    Three distinct tags also pin that the three variants are three, which is what
    a downstream `match` in Exec/Kzg/MultiOpen will rely on. -/
def polyErrorTag : PolyError → Nat
  | .openingError => 0
  | .samplingError => 1
  | .duplicatedQuery => 2

/-- KAT scaffolding: the closure at plonk/verifier.rs:651,
    `map_err(|_| Error::Opening)`, spelled out so the erasure is a checked fact
    rather than a comment. The definition itself belongs to Exec/Verifier, which
    owns that line; it is duplicated here only inside `section Kats`. -/
def erasePolyError : PolyError → Fault
  | _ => Fault.error Error.opening

/-- KAT scaffolding: is this `Fault` the plonk `Error::Opening` one? Written as a
    `match` because `Fault` has no `BEq` instance either. -/
def faultIsOpening (f : Fault) : Bool :=
  match f with
  | .error Error.opening => true
  | _ => false

/-- KAT scaffolding: a numeric tag per `Rotation` constructor, standing in for
    the `BEq` the type does not have. -/
def rotationTag : Rotation → Nat
  | .cur => 0
  | .next => 1
  | .prev => 2
  | .value _ => 3

/-- The three `PolyError` variants are distinct (mod.rs:38, :40, :43) and the
    erasure at plonk/verifier.rs:651 sends all three to the same plonk error -
    so through `verify_algebraic_constraints` the class is unobservable, while
    through `prepare` + `Guard::verify` (test.rs:370-380) it is. -/
def polyError_kats_ok : Bool :=
  polyErrorTag PolyError.openingError == 0 &&
    polyErrorTag PolyError.samplingError == 1 &&
    polyErrorTag PolyError.duplicatedQuery == 2 &&
    faultIsOpening (erasePolyError PolyError.openingError) &&
    faultIsOpening (erasePolyError PolyError.samplingError) &&
    faultIsOpening (erasePolyError PolyError.duplicatedQuery)

/-- `Rotation::cur()/prev()/next()` are `Rotation(0)`, `Rotation(-1)` and
    `Rotation(1)` (mod.rs:511-525), read back through `Rotation.int`. The rest is
    the representational caveat plus its reachable consumer: `cur` and `value 0`
    are distinct inhabitants (`rotationTag` differs) but the same rotation
    (`Rotation.int` agrees), and `rotate_omega` must match the hand-computed
    size-4 domain of `ZMod 17` - `omega = 3^(2^2) = 81 = 13`,
    `omega^{-1} = 13^{-1} = 4`, `omega^2 = 169 = 16` - giving
    `1 * omega^0 = 1`, `1 * omega^1 = 13`, `1 * omega^{-1} = 4`,
    `1 * omega^2 = 16`. -/
def rotation_kats_ok : Bool :=
  Rotation.int Rotation.cur == 0 &&
    Rotation.int Rotation.prev == -1 &&
    Rotation.int Rotation.next == 1 &&
    rotationTag Rotation.cur != rotationTag (Rotation.value 0) &&
    Rotation.int Rotation.cur == Rotation.int (Rotation.value 0) &&
    (match EvaluationDomain.new (F := Fr 17) polyFc17 1 2 with
     | .ok d =>
         (d.rotateOmega 1 Rotation.cur).val == 1 &&
           (d.rotateOmega 1 Rotation.next).val == 13 &&
           (d.rotateOmega 1 Rotation.prev).val == 4 &&
           (d.rotateOmega 1 (Rotation.value 2)).val == 16
     | .error _ => false)

end Kats

#eval polyError_kats_ok   -- expect true
#eval rotation_kats_ok   -- expect true

end Midfall.Halo2

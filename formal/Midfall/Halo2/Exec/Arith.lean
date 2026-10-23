-- |
-- Midfall.Halo2.Exec.Arith
--
-- Faithful port of `proofs/src/utils/arithmetic.rs`, plus the verifier-reachable
-- part of `proofs/src/utils/helpers.rs` (plan Section 4 module map, row
-- `utils/{arithmetic,helpers}.rs -> Exec/Arith`: `eval_polynomial`, inner
-- product, powers, `batch_invert`).
--
-- Port rules applied (plan Section 4): R1 provenance on every def, R2 names,
-- R3 iterator semantics (`zip` truncates to the shorter input), R4 panics become
-- `throw (Fault.panic "<path>:<line>")`, R5 `Nat`/`Int` with no wrapping unless
-- it can actually occur, R6 `Vec` -> `Array`, R7 `invert` returns `Option`,
-- `batch_invert` follows halo2 exactly (zeros skipped) and exponentiation is
-- explicit square-and-multiply, R9 traits become structures of functions, R10
-- computable and never `partial`.
--
-- Reachability. The verifier-reachable set grepped was plonk/{verifier,mod}.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, poly/kzg/*,
-- poly/{mod,query}.rs and solidity-verifier/src. Ported because reachable:
--   eval_polynomial       poly/query.rs:89, poly/kzg/mod.rs:476 (multi_prepare)
--   compute_inner_product plonk/verifier.rs:368
--   lagrange_interpolate  poly/kzg/mod.rs:475 (multi_prepare)
--   truncate              poly/kzg/mod.rs:457 (multi_prepare, truncated-challenges)
--   truncated_powers      poly/kzg/mod.rs:394,502,521 (multi_prepare)
--   powers                poly/kzg/mod.rs:397,505,524 (multi_prepare)
--   inner_product         poly/kzg/mod.rs:526 (multi_prepare)
--   evals_inner_product   poly/kzg/mod.rs:406 (multi_prepare)
--   batch_invert          ff-0.13.1/src/batch.rs:33, reached from
--                         arithmetic.rs:193 and from Exec/Domain (domain.rs:124,463)
--   byte_length           plonk/mod.rs:219 (VerifyingKey::bytes_length)
-- Skipped as not verifier-reachable, evidence recorded at each site below:
--   g_to_lagrange, parallelize, kate_division, trait MSM, trait FftGroup,
--   msm_inner_product (reachable but its type lives in Exec/Kzg), and most of
--   helpers.rs (the io::Read / io::Write serde plumbing).
--
-- Everything is generic over the scalar field (design decision D-P1): `Fr p` is
-- `ZMod p`, and the `ff::PrimeField` associated constants the Rust code reads off
-- the trait are carried explicitly by `FieldConsts` (rule R9), because there is no
-- BLS12-381 in the Lean ecosystem to read them from.

import Mathlib.Algebra.Field.ZMod
import Midfall.Common.Curve
import Midfall.Common.Codec
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

variable {F : Type} [Field F] [DecidableEq F]

/-- rust: std `usize::div_ceil` (used by arithmetic.rs:62 and :248). Lean's `Nat`
    has no `div_ceil`. `divCeil a 0 = 0` here, where Rust's division by zero
    panics; every caller guards the zero divisor and turns it into a `Fault.panic`. -/
def divCeil (a b : Nat) : Nat := (a + b - 1) / b

/-- rust: ff-0.13.1/src/lib.rs:195 (`PrimeField`) and :358
    (`WithSmallOrderMulGroup<3>`) - the associated constants the verifier-reachable
    code reads, as a structure of values (rule R9). Under D-P1 there is no concrete
    curve to project them from, so the BLS12-381 instantiation is supplied once in
    `Assumptions/Pairing.lean`.

    Only the reachable constants are carried: `ROOT_OF_UNITY_INV` and `TWO_INV` are
    read exclusively by `g_to_lagrange` (arithmetic.rs:35-36), which is prover-only,
    so they are not fields here. -/
structure FieldConsts (F : Type) where
  /-- rust: ff::PrimeField::NUM_BITS -/
  numBits : Nat
  /-- rust: ff::PrimeField::S (the two-adicity of p - 1) -/
  s : Nat
  /-- rust: ff::PrimeField::ROOT_OF_UNITY -/
  rootOfUnity : F
  /-- rust: ff::WithSmallOrderMulGroup::<3>::ZETA -/
  zeta : F

/-- rust: ff-0.13.1/src/lib.rs:178-191 (`Field::pow_vartime`). Explicit
    square-and-multiply over the binary expansion of the exponent, most significant
    bit first (rule R7). The Rust loop walks all four `u64` limbs from the top, so
    its leading zero limbs only do `res = res.square()` on `ONE`; dropping them is
    therefore not a behaviour change. -/
def powVartime (x : F) (e : Nat) : F :=
  (Nat.toDigits 2 e).foldl (fun res b => res * res * if b == '1' then x else 1) 1

/-- rust: ff-0.13.1/src/lib.rs:150 (`Field::invert`, which returns `CtOption`).
    Rule R7: the port returns `Option`, so a caller that unwraps it becomes an
    explicit panic site. -/
def invert (x : F) : Option F :=
  if x = 0 then none else some x⁻¹

/-- rust: ff-0.13.1/src/batch.rs:33-54 (`BatchInvert::batch_invert` for
    `I: IntoIterator<Item = &mut F>`). Montgomery's trick exactly as halo2 uses it:
    zero entries are *skipped* and left at zero rather than raising an error, and
    the value returned is the inverse of the product of the non-zero entries. The
    Rust fn mutates the slice in place and returns that inverse; the port returns
    both, and every verifier-reachable call site (arithmetic.rs:193, domain.rs:124,
    domain.rs:463) discards the second component.

    `batch.rs:42` is `acc.invert().unwrap()`. `acc` starts at `F::ONE` and is only
    ever multiplied by non-zero elements, so it is non-zero in a field and the
    unwrap cannot fire; rule R5 therefore does not make it a panic site. -/
def batchInvert (xs : Array F) : Array F × F :=
  let forward (st : F × List (F × F)) (p : F) : F × List (F × F) :=
    ((if p = 0 then st.1 else st.1 * p), st.2 ++ [(st.1, p)])
  let (acc, tmp) := xs.toList.foldl (init := (1, [])) forward
  let allinv := acc⁻¹
  let backward (q : F × F) (st : F × List F) : F × List F :=
    let pre := st.1
    let v := q.2
    let skip := v = 0
    ((if skip then pre else pre * v), (if skip then v else q.1 * pre) :: st.2)
  let (_acc, out) := tmp.foldr backward (allinv, [])
  (out.toArray, allinv)

/-- rust: proofs/src/utils/arithmetic.rs:54-56 (the private `evaluate` helper
    inside `eval_polynomial`): `poly.iter().rev().fold(ZERO, |acc, c| acc * point +
    c)`, i.e. Horner over the reversed coefficient list. -/
def evaluate (poly : Array F) (point : F) : F :=
  poly.toList.reverse.foldl (fun acc coeff => acc * point + coeff) 0

/-- rust: proofs/src/utils/arithmetic.rs:53-76 (`eval_polynomial`).

    The Rust fn has two branches that agree on the value they compute: the
    sequential Horner evaluation, and a split into `rayon::current_num_threads()`
    chunks whose partial results are re-scaled by `point^(chunk_idx * chunk_size)`
    and summed. The thread count is not observable in the result, so it is a
    parameter here rather than hidden global state.

    Panic sites kept:
    * `arithmetic.rs:62` `n.div_ceil(num_threads)` - Rust division by zero, which
      panics in every build profile. `rayon::current_num_threads()` is always
      `>= 1`, so the reference verifier never reaches it.
    * `arithmetic.rs:66` `poly.chunks(chunk_size)` panics when `chunk_size == 0`,
      i.e. when `n == 0`; that case always takes the sequential branch above
      (`(0 * 2 < num_threads` for `num_threads >= 1`), so it is unreachable here
      too and is not duplicated.

    `parts.chunks_mut(1).zip(poly.chunks(chunk_size))` truncates to the shorter
    input (rule R3). Since `ceil(n / ceil(n / t)) <= t` the truncation is a no-op,
    and the port iterates over the chunk index range directly. -/
def evalPolynomial (numThreads : Nat) (poly : Array F) (point : F) : Except Fault F := do
  let n := poly.size
  if n * 2 < numThreads then
    return evaluate poly point
  else
    if numThreads = 0 then
      throw (Fault.panic "proofs/src/utils/arithmetic.rs:62")
    let chunkSize := divCeil n numThreads
    let numChunks := divCeil n chunkSize
    let parts := (List.range numChunks).map fun chunkIdx =>
      let start := chunkIdx * chunkSize
      let chunk := (poly.toList.drop start).take chunkSize
      evaluate chunk.toArray point * powVartime point (chunkIdx * chunkSize)
    return parts.foldl (fun acc x => acc + x) 0

/-- rust: proofs/src/utils/arithmetic.rs:81-91 (`compute_inner_product`).
    `assert_eq!(a.len(), b.len())` at line 83 is a real panic site (rule R4) - the
    Rust doc comment says so out loud. The `zip` after it cannot truncate, because
    the lengths were just asserted equal. -/
def computeInnerProduct (a b : Array F) : Except Fault F := do
  unless a.size == b.size do
    throw (Fault.panic "proofs/src/utils/arithmetic.rs:83")
  return (List.zip a.toList b.toList).foldl (fun acc (x, y) => acc + x * y) 0

/-! rust: proofs/src/utils/arithmetic.rs:95-114 (`kate_division`) - NOT
    verifier-reachable: its only call sites are poly/kzg/mod.rs:271 and :312, both
    inside `multi_open` (poly/kzg/mod.rs:177-320), i.e. the prover. Body skipped.
    Note for whoever ports the prover: `a.len() - 1` at line 102 is a `usize`
    subtraction that underflows on an empty input, and the
    `q.iter_mut().rev().zip(a.rev())` at line 105 truncates to `min q a`. -/

/-! rust: proofs/src/utils/arithmetic.rs:118-167 (`parallelize`) - NOT
    verifier-reachable: the call sites are poly/mod.rs:198,220,402,421,442,480,486
    (prover-side `Polynomial` arithmetic), poly/kzg/params.rs:109,125,221 (the
    `ParamsKZG` prover parameters) and poly/domain.rs:329,355,369 (prover-only
    domain transforms, recorded in Exec/Domain). It is a rayon work splitter whose
    observable content is "apply `f` to every element exactly once, with the
    chunk's start index as the second argument"; the chunk boundaries are observable
    only through that index, which is why `divide_by_vanishing_poly`'s
    `index % t_evaluations.len()` is sensitive to them. Body skipped with the
    verifier port. -/

/-! rust: proofs/src/utils/arithmetic.rs:21-31 (`trait FftGroup`) - a marker trait
    with no methods, used only by the FFT helpers behind `g_to_lagrange` /
    `best_fft`, which are prover-only. Nothing to port: rule R9 turns
    behaviour-carrying traits into records of functions, and a marker trait carries
    none. -/

/-! rust: proofs/src/utils/arithmetic.rs:320-344 (`trait MSM`) - the eight-method
    MSM interface. Not ported here: it is the interface `Exec/Kzg/Msm` implements
    (`MSMKZG`), and the plan assigns `poly/kzg/msm.rs` to that module. -/

/-! rust: proofs/src/utils/arithmetic.rs:34-50 (`g_to_lagrange`) - NOT
    verifier-reachable: the call sites are poly/kzg/params.rs:52, :71 and :157, all
    on `ParamsKZG` (prover parameters: `downsize`, `downsize_lagrange`,
    `from_parts`). It also depends on `midnight_curves::fft::best_fft`, which has no
    verifier-reachable call site outside prover code. Body skipped. -/

/-- Port scaffolding for `lagrangeInterpolate`: split `flat` back into pieces shaped
    like `shapes`. This is the in-place
    `denoms.iter_mut().flat_map(|v| v.iter_mut()).batch_invert()` of
    arithmetic.rs:193, which Lean cannot express over a mutable nested vector. -/
def lagrangeReshape : List (List F) → List F → List (List F)
  | [], _ => []
  | xs :: rest, flat =>
      let (piece, flat') := flat.splitAt xs.length
      piece :: lagrangeReshape rest flat'

/-- Port scaffolding for `lagrangeInterpolate`: one step of the running product,
    i.e. arithmetic.rs:207-216. `tmp ++ [0]` and `[0] ++ tmp` are the two chained
    iterators of lines 210-211; `product`'s `resize` at line 207 pads to exactly
    `tmp.len() + 1` before every position is written, so the padding value is
    unobservable. -/
def lagrangeStep (tmp : List F) (xk denom : F) : List F :=
  List.zipWith (fun a b => a * (-denom * xk) + b * denom) (tmp ++ [0]) (0 :: tmp)

/-- Port scaffolding for `lagrangeInterpolate`: the outer loop of
    arithmetic.rs:196-223, including its two shape asserts. -/
def lagrangeGo (points : Array F) (n : Nat) (finalPoly : Array F) :
    List (Nat × List F × F) → Except Fault (Array F)
  | [] => .ok finalPoly
  | (j, ds, eval) :: rest => do
      let xs := ((List.range n).filter fun k => k ≠ j).map fun k => points.getD k 0
      let (tmp, product) :=
        (List.zip xs ds).foldl (init := ([1], []))
          fun st pair => (lagrangeStep st.1 pair.1 pair.2, st.1)
      unless tmp.length == n do
        throw (Fault.panic "proofs/src/utils/arithmetic.rs:218")
      unless product.length == n - 1 do
        throw (Fault.panic "proofs/src/utils/arithmetic.rs:219")
      let contribution := List.zipWith (fun f t => f + t * eval) finalPoly.toList tmp
      lagrangeGo points n contribution.toArray rest
  termination_by l => l.length

/-- rust: proofs/src/utils/arithmetic.rs:172-226 (`lagrange_interpolate`).
    Reachable at poly/kzg/mod.rs:475 (`multi_prepare`).

    The Rust bound is `F: Field + Ord` and lines 174-178 sort a copy of `points`
    then look for an adjacent equal pair. Only *equality* is observed, never the
    order, so the port needs no `Ord` on the field and checks the same property
    ("two values in `points` are equal") directly. This is the one place where the
    port does not mirror a Rust computation step for step, and it is deliberate.

    Panic sites: `:173` length mismatch, `:177` duplicate point, `:182` `evals[0]`
    (guarded by `points.len() == 1` plus the length assert), `:218`/`:219` the two
    shape asserts after the product loop. `points.len() - 1` at `:186`/`:198` is a
    `usize` subtraction, but the else-branch is only entered when `points.len() >=
    2`, so it cannot underflow. -/
def lagrangeInterpolate (points evals : Array F) : Except Fault (Array F) := do
  unless points.size == evals.size do
    throw (Fault.panic "proofs/src/utils/arithmetic.rs:173")
  if points.toList.any fun x => (points.toList.erase x).contains x then
    throw (Fault.panic "proofs/src/utils/arithmetic.rs:177")
  if points.size == 1 then
    match evals[0]? with
    | some v => return #[v]
    | none => throw (Fault.panic "proofs/src/utils/arithmetic.rs:182")
  let n := points.size
  let denoms : List (List F) :=
    (List.range n).map fun j =>
      ((List.range n).filter fun k => k ≠ j).map fun k => points.getD j 0 - points.getD k 0
  let inverted := (batchInvert ((denoms.flatMap id).toArray)).1.toList
  let denomsInv := lagrangeReshape denoms inverted
  let outer := List.zip (List.zip (List.range n) denomsInv) evals.toList
  lagrangeGo points n (List.toArray (List.replicate n 0))
    (outer.map fun ((j, ds), e) => (j, ds, e))

/-- rust: proofs/src/utils/arithmetic.rs:247-252 (`truncate`), gated on
    `feature = "truncated-challenges"` (rule R8: `Features.truncatedChallenges`).
    Reachable at poly/kzg/mod.rs:457.

    `F::NUM_BITS` is a parameter (`FieldConsts.numBits`) because there is no
    concrete field to read it from (D-P1). The Rust chain is: take the low
    `nb_bytes` of the little-endian repr, read them as a `BigUint`, print that in
    decimal and re-parse with `from_str_vartime`. Printing and re-parsing a
    canonical decimal is the identity on `BigUint`, and `from_str_vartime` reduces
    modulo `p`, so the port keeps the byte slice and the little-endian read and
    casts once. The `.unwrap()` at line 251 is therefore not a panic site:
    `BigUint::to_string` never yields the empty string, leading zeroes or
    non-digits, which are the only things `from_str_vartime` rejects.

    Divergence in shape, recorded because BASELINE.md fixes the reference profile as
    release: Rust's `&bytes[..nb_bytes]` panics when `nb_bytes > 32`, while
    `List.take` clamps. For a field with a 32-byte repr `NUM_BITS <= 256`, so
    `nb_bytes <= 16` and the two agree. -/
def truncate {p : ℕ} [Fact (Nat.Prime p)] (numBits : Nat) (scalar : Fr p) : Fr p :=
  let nbBytes := divCeil (divCeil numBits 8) 2
  let bytes := ByteArray.mk (((frToRepr scalar).data.toList.take nbBytes).toArray)
  Nat.cast (bytesToNatLE bytes)

/-- rust: proofs/src/utils/arithmetic.rs:259-261 (`powers`).
    `std::iter::successors(Some(ONE), |p| Some(base * p))` is the infinite stream
    `1, base, base^2, ...`. A computable Lean port cannot return an infinite
    iterator, so the length is an explicit argument: every verifier-reachable use is
    `powers(x).take(n).collect()` (poly/kzg/mod.rs:394,397,507). The elements are
    generated by the same recurrence rather than by `pow`, so the values match Rust
    exactly. -/
def powers (base : F) (n : Nat) : List F :=
  go n 1
where
  go : Nat → F → List F
    | 0, _ => []
    | m + 1, cur => cur :: go m (base * cur)
  termination_by m _ => m

/-- rust: proofs/src/utils/arithmetic.rs:255-257 (`truncated_powers`), gated on
    `feature = "truncated-challenges"`. Reachable at poly/kzg/mod.rs:394,502,521. -/
def truncatedPowers {p : ℕ} [Fact (Nat.Prime p)] (numBits : Nat) (base : Fr p) (n : Nat) :
    List (Fr p) :=
  (powers base n).map (truncate numBits)

/-- rust: proofs/src/utils/arithmetic.rs:263-273 (`inner_product`). Reachable at
    poly/kzg/mod.rs:526.

    The Rust signature is generic in `T: Mul<F> + Add<T> + Clone`; the only
    verifier-reachable call site passes `T = F` (`evals: Vec<E::Fr>`), so the port
    is stated at that instance rather than inventing a type class.

    `.reduce(..).unwrap()` at line 272 panics on an empty iterator - a real panic
    site, and easy to reach: `zip` truncates to the shorter input, so a `scalars`
    stream shorter than `polys` silently drops the tail, and an empty one empties
    the whole thing. -/
def innerProduct (polys : Array F) (scalars : List F) : Except Fault F :=
  match (List.zip polys.toList scalars).map (fun (p, s) => p * s) with
  | [] => .error (Fault.panic "proofs/src/utils/arithmetic.rs:272")
  | t :: rest => .ok (rest.foldl (fun acc x => acc + x) t)

/-! rust: proofs/src/utils/arithmetic.rs:275-299 (`msm_inner_product`) -
    verifier-reachable (poly/kzg/mod.rs:401 and :507, both in `multi_prepare`) but
    *not ported here*: its argument and result type is `MSMKZG<E>`, which the plan
    assigns to `Exec/Kzg/Msm` (Section 4 module map, row
    `poly/kzg/{mod,msm,params}.rs`). Porting it would mean inventing the MSM record
    in the wrong module, so it lands with the KZG work package. Two things worth
    recording now: the Rust body mutates each MSM with `scale(*s)` before copying
    its scalars/bases/labels out, and the `zip` at line 287 truncates to the shorter
    of `msms` and `scalars`, silently dropping un-scaled MSMs when fewer scalars
    than MSMs are passed. -/

/-- rust: proofs/src/utils/arithmetic.rs:306-317 (`evals_inner_product`).
    Reachable at poly/kzg/mod.rs:406.

    Two panic sites that are easy to miss:
    * `:310` `evals_set[0]` - out of bounds when the outer slice is empty.
    * `:313` `poly_evals[i]` - the result length comes from the *first* eval
      vector, and the inner loop runs `0..res.len()` over every later one, so any
      shorter eval vector indexes out of bounds. Longer ones are silently ignored.
    The `zip` at `:311` truncates to the shorter of `evals_set` and `scalars`, so
    extra eval vectors contribute nothing. -/
def evalsInnerProduct (evalsSet : Array (Array F)) (scalars : List F) :
    Except Fault (Array F) :=
  match evalsSet[0]? with
  | none => .error (Fault.panic "proofs/src/utils/arithmetic.rs:310")
  | some first => go (List.toArray (List.replicate first.size 0)) (List.zip evalsSet.toList scalars)
where
  go : Array F → List (Array F × F) → Except Fault (Array F)
    | acc, [] => .ok acc
    | acc, (polyEvals, s) :: rest =>
        if polyEvals.size < acc.size then
          .error (Fault.panic "proofs/src/utils/arithmetic.rs:313")
        else
          let summed := List.zipWith (fun a b => a + b * s) acc.toList polyEvals.toList
          go summed.toArray rest
  termination_by _ l => l.length

/-- rust: proofs/src/utils/helpers.rs:16-28 (`enum SerdeFormat`). Reachable: the
    verifier's VK reader and `bytes_length` take it (plonk/mod.rs:134,151,219). -/
inductive SerdeFormat where
  /-- rust: SerdeFormat::Processed -/
  | processed
  /-- rust: SerdeFormat::RawBytes -/
  | rawBytes
  /-- rust: SerdeFormat::RawBytesUnchecked -/
  | rawBytesUnchecked

/-- rust: proofs/src/utils/helpers.rs:47-52 (`byte_length`). Reachable through
    plonk/mod.rs:219 (`VerifyingKey::bytes_length`). The Rust fn is generic in `T:
    ProcessedSerdeObject` and reads the compressed repr length off the associated
    type; under D-P1 that length is a parameter, and for the only instantiation the
    verifier uses (`T = CS::Commitment = G1`) it is `Midfall.g1CompressedWidth`. -/
def byteLength (format : SerdeFormat) (reprLen : Nat) : Nat :=
  match format with
  | .processed => reprLen
  | .rawBytes | .rawBytesUnchecked => reprLen * 2

/-! rust: proofs/src/utils/helpers.rs:31-44 (`trait ProcessedSerdeObject`),
    :56-65 (`read_f`), :68-110 (its impl for curves), :115-122 (`pack`), :125-129
    (`unpack`), :132-143 (`read_polynomial_vec`), :146-155
    (`write_polynomial_slice`) and :159-162 (`polynomial_slice_byte_length`) - NOT
    verifier-reachable, so no bodies. Evidence: `read_f` is reached only from
    `Polynomial::read` (poly/mod.rs:315) and `read_polynomial_vec` only from
    `ProvingKey::read` (plonk/mod.rs:416); `write_polynomial_slice` and
    `polynomial_slice_byte_length` only from `ProvingKey::{write,bytes_length}`
    (plonk/mod.rs:384,362); `pack` / `unpack` have no call sites anywhere in the
    workspace outside their own definitions; `ProcessedSerdeObject::read` is used by
    `ParamsKZG::read_custom` (poly/kzg/params.rs:244-257), i.e. the prover parameter
    file. All of it is `io::Read` / `io::Write` plumbing over the serialized VK/PK,
    which belongs to the VK codec work package, not to Exec/Arith. -/

/-! ## Known-answer checks

Executable booleans, not proofs, in the style of `Midfall.keccak256_kats_ok`
(Midfall/Common/Keccak.lean). They pin the port against hand-computed values over
`ZMod 17`, small enough to check on paper. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A `Fr 17` value as a `Nat`, so the checks below compare through `BEq Nat` and do
    not depend on a `BEq` instance for `Except` or `ZMod`. -/
def fr17 (x : Fr 17) : Nat := x.val

/-- Unwrap an `Except Fault (Fr 17)` to a `Nat`, with a sentinel for the error case
    so a panic never accidentally matches an expected value. -/
def getFr17 (x : Except Fault (Fr 17)) : Nat :=
  match x with | .ok v => fr17 v | .error _ => 999

/-- `Except Fault _` is a panic (rather than a typed error). -/
def isPanic {α : Type} (x : Except Fault α) : Bool :=
  match x with | .error (Fault.panic _) => true | _ => false

/-- `eval_polynomial` on `2 + 3X + 5X^2 + 7X^3` at `X = 11` in `ZMod 17`:
    `2 + 33 + 605 + 9317 = 9957 = 17 * 585 + 12`. Both branches of the Rust
    implementation must agree, so the check runs the sequential branch
    (`num_threads = 10`, since `4 * 2 < 10`) and the chunked branch
    (`num_threads = 4`, chunk size 1), plus the empty polynomial and the
    division-by-zero panic at arithmetic.rs:62. -/
def evalPolynomial_kats_ok : Bool :=
  let poly : Array (Fr 17) := #[2, 3, 5, 7]
  getFr17 (evalPolynomial 10 poly 11) == 12 &&
    getFr17 (evalPolynomial 4 poly 11) == 12 &&
    getFr17 (evalPolynomial 1 poly 11) == 12 &&
    getFr17 (evalPolynomial 3 (poly := #[]) 5) == 0 &&
    isPanic (evalPolynomial 0 poly 11)

/-- `compute_inner_product <1,2,3|4,5,6> = 4 + 10 + 18 = 32 = 15 (mod 17)`, and the
    length assert at arithmetic.rs:83 fires on a mismatch. -/
def computeInnerProduct_kats_ok : Bool :=
  let a1 : Array (Fr 17) := #[1, 2, 3]
  let b1 : Array (Fr 17) := #[4, 5, 6]
  let a2 : Array (Fr 17) := #[1, 2]
  let b2 : Array (Fr 17) := #[3]
  let e0 : Array (Fr 17) := #[]
  getFr17 (computeInnerProduct a1 b1) == 15 &&
    isPanic (computeInnerProduct a2 b2) &&
    getFr17 (computeInnerProduct e0 e0) == 0

/-- `batch_invert` over `ZMod 17`: `3⁻¹ = 6`, `5⁻¹ = 7`, and the zero is left at
    zero (halo2 semantics, rule R7). The returned all-inverse is `(3*5)⁻¹ = 15⁻¹ =
    8`. The empty and all-zero cases pin that `acc` stays `ONE`, i.e. that the
    `unwrap` at batch.rs:42 really cannot fire. -/
def batchInvert_kats_ok : Bool :=
  let (out, allinv) := batchInvert (#[3, 0, 5] : Array (Fr 17))
  (out.map fr17) == #[6, 0, 7] && fr17 allinv == 8 &&
    (let (o, a) := batchInvert (#[] : Array (Fr 17)); o.size == 0 && fr17 a == 1) &&
    (let (o, a) := batchInvert (#[0, 0] : Array (Fr 17)); (o.map fr17) == #[0, 0] && fr17 a == 1) &&
    (let (o, _) := batchInvert (#[6, 7] : Array (Fr 17)); (o.map fr17) == #[3, 5])

/-- More reachable defs, checked against `ZMod 17` arithmetic: `powers`, the
    truncated power stream (16 bytes kept, so `truncate` is the identity on values
    below `2^128`), `powVartime`, `invert`, the `inner_product` empty panic and its
    `zip` truncation, a Lagrange interpolation round trip plus its duplicate-point
    panic, `evals_inner_product` and its short-row panic, and `byteLength`. -/
def arithExtra_kats_ok : Bool :=
  let pw : List (Fr 17) := powers 3 5
  (pw.map fr17) == [1, 3, 9, 10, 13] &&
    ((truncatedPowers 255 (3 : Fr 17) 5).map fr17 == pw.map fr17) &&
    fr17 (powVartime (3 : Fr 17) 5) == 5 &&
    (match invert (3 : Fr 17) with | some v => fr17 v == 6 | none => false) &&
    (match invert (0 : Fr 17) with | none => true | some _ => false) &&
    (match innerProduct (#[1, 2, 3] : Array (Fr 17)) [1, 1] with
     | .ok v => fr17 v == 3
     | .error _ => false) &&
    isPanic (innerProduct (#[] : Array (Fr 17)) [1]) &&
    (match lagrangeInterpolate (#[0, 1] : Array (Fr 17)) #[1, 2] with
     | .ok v => (v.map fr17) == #[1, 1]
     | .error _ => false) &&
    isPanic (lagrangeInterpolate (#[2, 2] : Array (Fr 17)) #[1, 2]) &&
    (match lagrangeInterpolate (#[7] : Array (Fr 17)) #[9] with
     | .ok v => (v.map fr17) == #[9]
     | .error _ => false) &&
    (match evalsInnerProduct (#[#[1, 2], #[3, 4]] : Array (Array (Fr 17))) [1, 2] with
     | .ok v => (v.map fr17) == #[7, 10]
     | .error _ => false) &&
    isPanic (evalsInnerProduct (#[#[1, 2], #[3]] : Array (Array (Fr 17))) [1, 1]) &&
    byteLength SerdeFormat.processed 48 == 48 &&
    byteLength SerdeFormat.rawBytes 48 == 96

end Kats

#eval evalPolynomial_kats_ok
#eval computeInnerProduct_kats_ok
#eval batchInvert_kats_ok
#eval arithExtra_kats_ok

end Midfall.Halo2

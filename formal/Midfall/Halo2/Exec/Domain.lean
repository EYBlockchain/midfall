-- |
-- Midfall.Halo2.Exec.Domain
--
-- Faithful port of the verifier-reachable subset of
-- `proofs/src/poly/domain.rs` (plan Section 4 module map, row
-- `poly/{mod,domain,query,commitment}.rs -> Exec/{Poly,Domain,Query,Pcs}`:
-- `Rotation`, `rotate_omega`, `l_i_range`, quotient degree).
--
-- Port rules: R1 provenance, R2 names (`l_i_range` -> `lIRange`,
-- `get_omega` -> `getOmega`), R3 iterator semantics, R4 panics ->
-- `throw (Fault.panic "<path>:<line>")`, R5 `Nat`/`Int`, R6 `Vec` -> `Array`,
-- R7 batch inversion via `Exec/Arith.batchInvert` and exponentiation via
-- `Exec/Arith.powVartime`, R9/R10 as in Exec/Arith.
--
-- Reachability. Grepped over plonk/{verifier,mod}.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, poly/kzg/*,
-- poly/{mod,query}.rs and solidity-verifier/src. Ported because reachable:
--   EvaluationDomain (the struct)  plonk/mod.rs:62 (VerifyingKey.domain)
--   new                             plonk/mod.rs:175 (VerifyingKey::read_from_cs)
--   get_omega                       plonk/verifier.rs:316, solidity-verifier/src/lowering/vk.rs:113
--   get_omega_inv                   plonk/verifier.rs:321, lowering/vk.rs:114
--   get_quotient_poly_degree        plonk/verifier.rs:288
--   rotate_omega                    plonk/verifier.rs:603,614,638,
--                                   plonk/permutation/verifier.rs:151,152,
--                                   plonk/logup/verifier.rs:178
--   l_i_range                       plonk/verifier.rs:345,444, plonk/mod.rs:510
--   Rotation                        poly/mod.rs:509, used by all of the above
-- Not verifier-reachable, so no bodies (evidence at each site below): the FFT
-- transport (`lagrange_to_coeff`, `coeff_to_lagrange`, `coeff_to_extended`,
-- `extended_to_coeff`, `extended_to_lagrange`, `ifft`, `distribute_powers_zeta`,
-- `divide_by_vanishing_poly`), the `Polynomial` constructors (`lagrange_from_vec`,
-- `coeff_from_vec`, `empty_*`, `constant_*`), the remaining accessors (`k`,
-- `extended_k`, `extended_len`, `get_extended_omega`) and `pinned` /
-- `PinnedEvaluationDomain`.
--
-- The Rust `EvaluationDomain<F>` is built for `F: WithSmallOrderMulGroup<3>` and
-- reads `F::S`, `F::ROOT_OF_UNITY` and `F::ZETA` off the type. Under design
-- decision D-P1 there is no concrete field to read them from, so they arrive as a
-- `FieldConsts` record (rule R9) - the same shape Exec/Arith uses.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Error

namespace Midfall.Halo2

variable {F : Type} [Field F] [DecidableEq F]

/-- rust: proofs/src/poly/domain.rs:17-32 (struct EvaluationDomain). Field order
    is the Rust field order (rule R1). The Rust `n`, `quotient_poly_degree` are
    `u64` and `k`, `extended_k` are `u32`; all four become `Nat` (rule R5) - no
    wrapping is possible because the values are powers of two bounded by `F::S`
    (checked at domain.rs:53). -/
structure EvaluationDomain (F : Type) where
  /-- rust: domain.rs:18 (n: u64) -/
  n : Nat
  /-- rust: domain.rs:19 (k: u32) -/
  k : Nat
  /-- rust: domain.rs:20 (extended_k: u32) -/
  extendedK : Nat
  /-- rust: domain.rs:21 (omega: F) -/
  omega : F
  /-- rust: domain.rs:22 (omega_inv: F) -/
  omegaInv : F
  /-- rust: domain.rs:23 (extended_omega: F) -/
  extendedOmega : F
  /-- rust: domain.rs:24 (extended_omega_inv: F) -/
  extendedOmegaInv : F
  /-- rust: domain.rs:25 (g_coset: F) -/
  gCoset : F
  /-- rust: domain.rs:26 (g_coset_inv: F) -/
  gCosetInv : F
  /-- rust: domain.rs:27 (quotient_poly_degree: u64) -/
  quotientPolyDegree : Nat
  /-- rust: domain.rs:28 (ifft_divisor: F) -/
  ifftDivisor : F
  /-- rust: domain.rs:29 (extended_ifft_divisor: F) -/
  extendedIfftDivisor : F
  /-- rust: domain.rs:30 (t_evaluations: Vec<F>) -/
  tEvaluations : Array F
  /-- rust: domain.rs:31 (barycentric_weight: F) -/
  barycentricWeight : F

/-- rust: proofs/src/poly/mod.rs:509 (`pub struct Rotation(pub i32)`) and
    :511-527 (`cur`, `next`, `prev`). Exec/Circuit.lean models `Rotation` as a
    closed inductive because that is the form the constraint-system port needs;
    this recovers the integer the Rust tuple field `.0` carries, which is what
    `rotate_omega` and `l_i_range` read. -/
def Rotation.int : Rotation → Int
  | .cur => 0
  | .next => 1
  | .prev => -1
  | .value v => v

/-- rust: proofs/src/poly/domain.rs:37-142 (`EvaluationDomain::new`).

    Panic sites and divergences, all recorded:
    * `domain.rs:39` `(j - 1) as u64` is a `u32` subtraction. In the reference
      (release) profile it *wraps* to `2^32 - 1` when `j = 0`; in debug it
      panics. `Nat` subtraction here saturates at 0 instead. The port does not
      emulate either, because `j = cs.degree()` and `ConstraintSystem::degree`
      ends in `.unwrap_or(1)` (plonk/circuit.rs:2443-2456), so `j >= 1` always.
    * `domain.rs:42` `1u64 << k` panics for `k >= 64` (shift overflow, both
      profiles). Unreachable for the verifier: `VerifyingKey::read_from_cs`
      rejects `k > F::S` first (plonk/mod.rs:168-173) and `F::S = 32`.
    * `domain.rs:48` `n * quotient_poly_degree` is `u64` multiplication: it wraps in
      the reference release profile and panics in debug. Not emulated (rule R5):
      with `k <= 32` and a single-digit `cs.degree()`, the product is nowhere near
      `2^64`.
    * `domain.rs:53` `assert!(extended_k <= F::S)` - a real panic, kept.
    * `domain.rs:91-97` is an unbounded `loop { .. if cur == orig { break } }`
      and `domain.rs:98` asserts that it ran `1 << (extended_k - k)` times. A
      computable Lean port cannot loop unboundedly (rule R10), so the port builds
      exactly `m = 2^(extended_k - k)` points and then checks the condition the
      Rust loop and its assert together pin: `step^i != 1` for `1 <= i < m` and
      `step^m = 1`. If a caller hands over a `FieldConsts` whose `rootOfUnity` is
      not a primitive `2^S`-th root, Rust would either panic at :98 or spin
      forever; the port always fails at :98. That is the one place where the two
      can differ, and it is a malformed-input case, not a verifier case.
    * `domain.rs:101-103` subtracts 1 from every `t_evaluation` and `:117-124`
      batch-inverts them. A zero `t_evaluation` (i.e. a coset point that is also
      an `n`-th root of unity) is *silently left at zero* by `batch_invert`
      rather than raising - see Exec/Arith.batchInvert. -/
def EvaluationDomain.new (fc : FieldConsts F) (j k : Nat) :
    Except Fault (EvaluationDomain F) := do
  -- domain.rs:39
  let quotientPolyDegree := j - 1
  -- domain.rs:42
  let n := 2 ^ k
  -- domain.rs:47-50
  let target := n * quotientPolyDegree
  let extendedK := extLoop (target + 1) k target
  -- domain.rs:53
  unless extendedK ≤ fc.s do
    throw (Fault.panic "proofs/src/poly/domain.rs:53")
  -- domain.rs:55-63: extended_omega = root_of_unity^(2^(S - extended_k))
  let extendedOmega := repeatSquare (fc.s - extendedK) fc.rootOfUnity
  -- domain.rs:64: seeded with the value to invert, inverted in the chain below
  let extendedOmegaInv := extendedOmega
  -- domain.rs:71-76: omega = extended_omega^(2^(extended_k - k))
  let omega := repeatSquare (extendedK - k) extendedOmega
  let omegaInv := omega
  -- domain.rs:81-82
  let gCoset := fc.zeta
  let gCosetInv := gCoset * gCoset
  -- domain.rs:84-99
  let m := 2 ^ (extendedK - k)
  let orig := powVartime gCoset n
  let step := powVartime extendedOmega n
  let pts := cosetPts m orig step
  let early := ((List.range m).drop 1).map fun i => powVartime step i
  unless (early.all fun q => q ≠ 1) && powVartime step m == 1 do
    throw (Fault.panic "proofs/src/poly/domain.rs:98")
  -- domain.rs:101-103
  let tEvaluations := (pts.map fun c => c - 1).toArray
  -- domain.rs:109-114
  let ifftDivisor := Nat.cast (2 ^ k)
  let extendedIfftDivisor := Nat.cast (2 ^ extendedK)
  let barycentricWeight := Nat.cast n
  -- domain.rs:117-124: one batch inversion over the chained iterator, in the
  -- Rust chain order (t_evaluations, then the five scalars).
  let chain := (tEvaluations.toList ++
      [ifftDivisor, extendedIfftDivisor, barycentricWeight, extendedOmegaInv, omegaInv]).toArray
  let inv := (batchInvert chain).1.toList
  let (tEvals', rest) := inv.splitAt m
  match rest with
  | [ifftDivisor', extendedIfftDivisor', barycentricWeight', extendedOmegaInv', omegaInv'] =>
      return {
        n := n
        k := k
        extendedK := extendedK
        omega := omega
        omegaInv := omegaInv'
        extendedOmega := extendedOmega
        extendedOmegaInv := extendedOmegaInv'
        gCoset := gCoset
        gCosetInv := gCosetInv
        quotientPolyDegree := quotientPolyDegree
        ifftDivisor := ifftDivisor'
        extendedIfftDivisor := extendedIfftDivisor'
        tEvaluations := tEvals'.toArray
        barycentricWeight := barycentricWeight'
      }
  | _ => throw (Fault.panic "proofs/src/poly/domain.rs:117")
where
  /-- rust: domain.rs:47-50 (`while (1 << extended_k) < n * quotient_poly_degree`).
      `2^(k+i) >= i + 1`, so `target + 1` iterations always suffice and the fuel
      cannot run out; it is there only to keep the definition structurally
      terminating (rule R10). -/
  extLoop : Nat → Nat → Nat → Nat
    | 0, ek, _ => ek
    | fuel + 1, ek, target => if 2 ^ ek < target then extLoop fuel (ek + 1) target else ek

  /-- rust: `for _ in a..b { x = x.square() }` - a saturating count of
      squarings, which is what an empty Rust range means when `b < a`. -/
  repeatSquare : Nat → F → F
    | 0, x => x
    | i + 1, x => repeatSquare i (x * x)

  /-- rust: domain.rs:91-93 (`loop { t_evaluations.push(cur); cur *= &step; }`)
      truncated to the length the assert at :98 pins. -/
  cosetPts : Nat → F → F → List F
    | 0, _, _ => []
    | i + 1, cur, step => cur :: cosetPts i (cur * step) step

/-- rust: proofs/src/poly/domain.rs:393-395 (`get_omega`). Reachable at
    plonk/verifier.rs:316. -/
def EvaluationDomain.getOmega (d : EvaluationDomain F) : F := d.omega

/-- rust: proofs/src/poly/domain.rs:399-401 (`get_omega_inv`). Reachable at
    plonk/verifier.rs:321. -/
def EvaluationDomain.getOmegaInv (d : EvaluationDomain F) : F := d.omegaInv

/-- rust: proofs/src/poly/domain.rs:476-478 (`get_quotient_poly_degree`).
    Reachable at plonk/verifier.rs:288: it is how many quotient-limb commitments
    the verifier reads out of the proof (unless the `single-h-commitment` feature
    pins it to 1). -/
def EvaluationDomain.getQuotientPolyDegree (d : EvaluationDomain F) : Nat :=
  d.quotientPolyDegree

/-- rust: proofs/src/poly/domain.rs:410-418 (`rotate_omega`). Reachable at
    plonk/verifier.rs:603,614,638, plonk/permutation/verifier.rs:151,152 and
    plonk/logup/verifier.rs:178.

    `rotation.0 >= 0` selects `omega^r` and the negative branch
    `omega_inv^|r|`; `pow_vartime([rotation.0 as u64])` is a lossless widening for
    a non-negative `i32`, so `Int.toNat` / `Int.natAbs` reproduce it exactly
    (rule R5). Note the asymmetry the port has to keep: `i32::MIN` negated through
    `(rotation.0 as i64).unsigned_abs()` is `2^31`, not `-2^31` wrapped - the
    `as i64` widening happens first, so no overflow occurs in either profile. -/
def EvaluationDomain.rotateOmega (d : EvaluationDomain F) (value : F) (rotation : Rotation) : F :=
  let r := rotation.int
  if 0 ≤ r then
    value * powVartime (d.getOmega) r.toNat
  else
    value * powVartime (d.getOmegaInv) (Int.natAbs r)

/-- rust: proofs/src/poly/domain.rs:448-473 (`l_i_range`). Reachable at
    plonk/verifier.rs:345 and :444, and plonk/mod.rs:510.

    The Rust takes `I: IntoIterator<Item = i32> + Clone` and walks it twice (once
    to build `x - omega^r`, once to scale and rotate the inverted results); the
    port takes a `List Int`, which is the same thing with the same order, and the
    second pass `zip`s against `results` so it cannot get out of step (rule R3).

    No panic site, but a silent-degradation one: `results.iter_mut().batch_invert()`
    at :463 leaves a zero at zero. If `x` is itself a domain point `omega^r` for one
    of the requested `r`, that entry comes back `0` instead of `l_r(x) = 1`. The
    reference verifier relies on the squeezed challenge `x` missing the domain. -/
def EvaluationDomain.lIRange (d : EvaluationDomain F) (x xn : F) (rotations : List Int) :
    Array F :=
  -- domain.rs:456-464
  let results := (batchInvert ((rotations.map fun r =>
      x - d.rotateOmega 1 (Rotation.value r))).toArray).1.toList
  -- domain.rs:466-470
  let common := (xn - 1) * d.barycentricWeight
  (List.zipWith (fun res r => d.rotateOmega (res * common) (Rotation.value r)) results rotations).toArray

/-! rust: proofs/src/poly/domain.rs:147-154 (`lagrange_from_vec`), :159-166
    (`coeff_from_vec`), :169-174 (`empty_coeff`), :178-183 (`empty_lagrange`),
    :187-192 (`empty_lagrange_rational`), :195-200 (`constant_lagrange`),
    :204-209 (`empty_extended`), :213-218 (`constant_extended`) - NOT
    verifier-reachable. Evidence: `lagrange_from_vec` only at
    plonk/trash/prover.rs:48; `coeff_from_vec`, `empty_lagrange_rational`,
    `constant_lagrange`, `empty_extended` and `constant_extended` have no call
    sites in the reachable set at all; `empty_coeff` only at poly/kzg/mod.rs:681,
    :686, :691, which are inside `mod tests` (poly/kzg/mod.rs:577 onward);
    `empty_lagrange` only at plonk/trash/prover.rs:58 and poly/kzg/params.rs:347
    (also `mod tests`). They all build a `Polynomial<F, B>`, which the verifier
    never touches. -/

/-! rust: proofs/src/poly/domain.rs:224-234 (`lagrange_to_coeff`), :238-247
    (`coeff_to_lagrange`), :251-265 (`coeff_to_extended`), :272-288
    (`extended_to_coeff`), :295-317 (`extended_to_lagrange`), :321-340
    (`divide_by_vanishing_poly`), :349-365 (`distribute_powers_zeta`) and :367-375
    (`ifft`) - NOT verifier-reachable. Evidence: `lagrange_to_coeff` at
    plonk/trash/prover.rs:63 and plonk/mod.rs:419 (inside `ProvingKey::read`,
    i.e. the proving key); `coeff_to_lagrange` and `coeff_to_extended` at
    poly/mod.rs:130, :159 and plonk/mod.rs:423 (`ProvingKey::read` again);
    `extended_to_coeff`, `extended_to_lagrange`, `divide_by_vanishing_poly`,
    `distribute_powers_zeta` and `ifft` have no call sites outside this file and
    the prover. They are the FFT transport, and every one of them bottoms out in
    `midnight_curves::fft::best_fft`, which has no verifier-reachable call site. -/

/-! rust: proofs/src/poly/domain.rs:378-380 (`k`), :383-385 (`extended_k`),
    :388-390 (`extended_len`), :404-406 (`get_extended_omega`), :483-489
    (`pinned`) and :492-499 (`PinnedEvaluationDomain`) - not ported as defs.
    `k`, `extended_k` and `extended_len` are read only by prover code
    (poly/mod.rs:144, :152 and the `PolynomialRepresentation` instances) and by VK
    serialization (plonk/mod.rs:97, `VerifyingKey::write`); `get_extended_omega`
    only at poly/mod.rs:148. The data is still available as the `k` /
    `extendedK` structure fields. `pinned` *is* on the VK construction path
    (plonk/mod.rs:271, inside `from_parts`, where its `Debug` rendering feeds the
    Blake2b hash that produces `transcript_repr`), but its content is only `k`,
    `extended_k` and `omega` formatted as a string - that belongs to the VK
    hashing work package (Exec/VerifyingKey, `hash_into` / `transcript_repr`), not
    to the domain arithmetic, so it is deliberately not duplicated here. -/

/-! ## Known-answer checks

Same style as Exec/Arith: executable booleans over `ZMod 17`, whose
multiplicative group has order 16, so `S = 4` and `3` is a primitive
`2^4`-th root of unity. `ZMod 17^x` has no element of order 3, so `zeta` cannot
be a genuine cube root here; the checks below exercise the arithmetic that does
not depend on it (`new`'s root-of-unity chain, `rotate_omega`, `l_i_range`) and
use `zeta = 2` as an arbitrary placeholder. -/

section DomainKats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def fr17d (x : Fr 17) : Nat := x.val

/-- The `ZMod 17` constants: `p - 1 = 16 = 2^4`, so `S = 4` and
    `ROOT_OF_UNITY = 3` (order 16). -/
def fc17 : FieldConsts (Fr 17) :=
  { numBits := 5, s := 4, rootOfUnity := 3, zeta := 2 }

/-- `EvaluationDomain::new(1, 2)` over `ZMod 17`. Hand-computed:
    `quotient_poly_degree = 0`, `n = 4`, `extended_k = 2`,
    `extended_omega = 3^(2^2) = 81 = 13`, `omega = 13`, `m = 1`,
    `orig = zeta^n = 2^4 = 16`, `step = 13^4 = 1`, so `t_evaluations = [16 - 1]`
    and the batch inversion gives `[15⁻¹] = [8]`; `1/n = 4⁻¹ = 13` and
    `omega⁻¹ = 13⁻¹ = 4`. -/
def domainNew_kats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 1 2 with
  | .error _ => false
  | .ok d =>
      fr17d d.omega == 13 && fr17d d.omegaInv == 4 &&
        fr17d d.extendedOmega == 13 && fr17d d.extendedOmegaInv == 4 &&
        (d.tEvaluations.map fr17d) == #[8] &&
        fr17d d.barycentricWeight == 13 &&
        fr17d d.ifftDivisor == 13 && fr17d d.extendedIfftDivisor == 13 &&
        d.n == 4 && d.k == 2 && d.extendedK == 2 && d.quotientPolyDegree == 0 &&
        fr17d d.gCoset == 2 && fr17d d.gCosetInv == 4

/-- `new` rejects `extended_k > S` (domain.rs:53). Over `ZMod 17` with `S = 4`,
    asking for `k = 5` needs `2^5 = 32 > 16` points, so `extended_k >= 5 > 4`. -/
def domainPanic_kats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 2 5 with
  | .error (Fault.panic "proofs/src/poly/domain.rs:53") => true
  | _ => false

/-- `rotate_omega` and `l_i_range` on the size-4 domain
    `{1, 13, 16, 4}` of `ZMod 17`, with `omega = 13` and `barycentric_weight =
    13`. `l_i_range(2, 2^4, [0, 1, -1])` must be `[8, 6, 1]`:
    `common = (16 - 1)/4 = 15 * 13 = 8`, so
    `l_0 = 8/(2-1) = 8`,
    `l_1 = 13 * 8/(2-13) = 104/(-11) = 2/6 = 2*3 = 6`,
    `l_-1 = 4 * 8/(2-4) = 32/(-2) = 15/15 = 1`.
    Cross-checked against the direct Lagrange formula for `l_0` and `l_1` over
    the four-point domain. -/
def lIRange_kats_ok : Bool :=
  match EvaluationDomain.new (F := Fr 17) fc17 1 2 with
  | .error _ => false
  | .ok d =>
      ((d.rotateOmega 1 (Rotation.value 1)).val) == 13 &&
        ((d.rotateOmega 1 (Rotation.value (-1))).val) == 4 &&
        ((d.rotateOmega 2 (Rotation.cur)).val) == 2 &&
        ((d.lIRange 2 16 [0, 1, -1]).map fr17d) == #[8, 6, 1] &&
        -- x = omega is a domain point (13 = omega, so x^n = 13^4 = 1): both the
        -- numerator (xn - 1 = 0) and the skipped inversion of the zero entry
        -- collapse, and l_i_range returns zeros instead of l_1(omega) = 1.
        ((d.lIRange 13 1 [0, 1]).map fr17d) == #[0, 0]

end DomainKats

#eval domainNew_kats_ok
#eval domainPanic_kats_ok
#eval lIRange_kats_ok

end Midfall.Halo2

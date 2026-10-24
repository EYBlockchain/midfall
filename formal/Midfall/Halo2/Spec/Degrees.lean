-- |
-- Midfall.Halo2.Spec.Degrees
--
-- The error-budget *degree* functions that plan Section 9.4's `roundErr`,
-- `ksErr` and `chalMass` consume (plan Section 6, Phase 4 skeleton). Section 10
-- puts the paper proof first, so this file is the combinatorial skeleton of
-- `docs/security.tex` and nothing more: every quantity here is a count of BAD
-- POINTS for one squeezed challenge, read off the ported constraint system
-- (Exec/Circuit.lean), the ported domain (Exec/Domain.lean) and the ported
-- multi-open bookkeeping (Exec/Kzg/Utils.lean). Nothing here is a probability,
-- and the only thing proved is the arithmetic behind the constant 3 in
-- `chalMass`.
--
-- WHY `Midfall.Halo2.Spec` AND NOT `Midfall.Security`. Plan 9.4 writes `Chal`,
-- `chalMass`, `roundErr` and `ksErr` in `namespace Midfall.Security` and says of
-- the degrees "defined in Spec/Degrees (paper proof first)". The degrees are
-- functions of a `CircuitIndex`, which lives in `Midfall.Halo2.Spec
-- (Spec/Relation.lean)`, and `Midfall.Security` must not import the Spec layer
-- backwards, so the cluster is defined here. `Midfall.Security.Chal` and
-- `Midfall.Security.chalMass` already exist in Security/Challenges.lean with the
-- same shape over `ℝ≥0∞`; they are not redefined under a different meaning and
-- collapsing the two is a Phase 4 decision (raised in this package's report).
--
-- R-2 IS THE REASON THIS FILE EXISTS. docs/REVIEW.md R-2 (three manifestations)
-- says the whole argument rests on "the squeezed challenge misses a finite set
-- of bad points", and the round errors are exactly where that assumption is
-- quantified. So the bad-point SETS are spelled out here where they are
-- computable (`badPointsX`, `badPointsX3`, `badPointsBetaCount`) and not only
-- their cardinalities; where a set depends on the proof rather than on the
-- circuit, only the count is defined.
--
-- CONSERVATISM RULE. Where the Rust does not name a number, the definition takes
-- the largest value that is still sound and says so in a `/-! ... -/` note; those
-- are the four entries marked CONSERVATIVE below (degTheta, degBeta, srsBound,
-- verifierQueries) plus the `x3` row of `roundErr`, which follows the plan
-- verbatim even though `badPointsX3Count` is the honest number.
--
-- Imports are Exec modules read-only plus Spec/Relation; nothing in this file
-- depends on Exec/Verifier or Exec/Native, which are being edited in parallel.

import Mathlib.Basic.NNReal.Defs
import Midfall.Assumptions.Pairing
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Features
import Midfall.Halo2.Exec.Kzg.Utils
import Midfall.Halo2.Exec.Logup
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Trash
import Midfall.Halo2.Spec.Relation

namespace Midfall.Halo2.Spec

open scoped NNReal
open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### 1. The numbers a `CircuitIndex` owns -/

/-! `CircuitIndex.n` lives in Spec/Relation.lean (it is needed there by `rowAt`
    and `usable`); this file imports it rather than redefining it. rust:
    plonk/mod.rs:122-124 (`VerifyingKey::n`) and poly/domain.rs:42
    (`n = 1 << k`), so `n = 2^k`; Exec/VerifyingKey's `domainConsistent` is the
    same fact at VK level. -/

/-- The constraint-system degree, made total. rust: plonk/circuit.rs:2443-2467
    (`ConstraintSystem::degree`), ported as `ConstraintSystem.degree`, which is
    `Except`-valued only because of the two logUp panics of docs/REVIEW.md R-13
    (logup.rs:237 division by zero, logup.rs:318 `chunks(0)`).
    WHERE USED: plan 9.4's `.x` round error (`idx.cs.degree * idx.n + idx.n`) and
    every degree that feeds it. The `0` fallback is never read under
    `WellFormed.csDegreeOk`: a CS whose degree panics aborts the verifier before
    it reads a proof byte (R-13), so it accepts nothing and no bound is needed. -/
def CircuitIndex.csDegree (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.cs.degree with
  | .ok d => d
  | .error _ => 0

/-- The blinding factors, made total. rust: plonk/circuit.rs:2472-2512
    (`ConstraintSystem::blinding_factors`), ported as
    `ConstraintSystem.blindingFactors`.
    WHERE USED: the permutation's third opening point
    `x·ω^-(blinding_factors+1)` (plonk/permutation/verifier.rs:150-152, ported as
    `Permutation.Evaluated.queries`), which is what puts a THIRD point into the
    largest permutation point set and therefore drives `maxSetSize` and the `x3`
    round error. Same fallback caveat as `csDegree`. -/
def CircuitIndex.blindingFactors (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.cs.blindingFactors with
  | .ok b => b
  | .error _ => 0

/-- How many permutation product polynomials, i.e. the number of column chunks.
    rust: plonk/permutation/verifier.rs:41 (`let chunk_len = vk.cs_degree - 2`)
    and :45 (`columns.chunks(chunk_len)`), ported as
    `Permutation.readProductCommitments`; Exec/VerifyingKey.lean's
    `permutationCommitmentsMatch` states the same `divCeil` against the VK's
    commitment count.
    WHERE USED: the number of permutation identities folded by `y`
    (`numConstraints`) and the number of distinct point sets the permutation
    contributes to `queryShapes`. -/
def CircuitIndex.numPermSets (idx : CircuitIndex (Fr p)) : Nat :=
  divCeil idx.cs.permutation.columns.size (idx.csDegree - 2)

/-- The sigma side of the same three-way zip. rust: plonk/permutation.rs:236-240
    zips sets x column-chunks x permutation-eval-chunks, so the SHORTEST wins and
    whole identities are dropped silently with no error (docs/REVIEW.md R-15).
    The eval-chunk count is the sigma count, which at CircuitIndex level is
    `PermutationAssembly.sigmaCommitments`. WHERE USED: `numPermIdentities`. -/
def CircuitIndex.numPermEvalChunks (idx : CircuitIndex (Fr p)) : Nat :=
  divCeil idx.perm.sigmaCommitments.size (idx.csDegree - 2)

/-- The number of degree-bounded logUp chunks, made total.
    rust: plonk/logup.rs:316-319 (`BatchedArgument::num_chunks`), ported as
    `LogupBatchedArgument.numChunks`; the verifier reaches it at
    plonk/verifier.rs:189 through `chunk_by_degree`.
    TOTALITY: `numChunks` is `Except`-valued because `.chunks(nb)` panics at
    logup.rs:318 when `nb = 0` (docs/REVIEW.md R-13). `divCeil` is nonincreasing
    in the divisor and `nb >= 1` whenever it does not panic, so
    `num_chunks <= input_expressions.len()` always, and the fallback is that
    upper bound rather than a silent `0`.
    WHERE USED: `numLogupIdentities` (one helper identity per chunk) and the
    number of helper commitments opened at `x` in `queryShapes`, which is what
    makes `maxPolysPerSet` grow with chunking. -/
def LogupBatchedArgument.numChunksTotal {F : Type} (L : LogupBatchedArgument F)
    (csDegree : Nat) : Nat :=
  match L.numChunks csDegree with
  | .ok n => n
  | .error _ => L.inputExpressions.size

/-- The compression width a batched logUp argument feeds to `theta`.
    rust: plonk/logup.rs:286-291 - `BatchedArgument::new` transposes the caller's
    `[(inputs, table)]` map into `input_expressions[parallel][width]` and
    `table_expressions[width]`, so a well-formed argument has
    `input_expressions[j].len() == table_expressions.len() == width` for every
    `j`. Taking the `max` over both is the conservative reading of a hand-built
    argument that violates it: docs/REVIEW.md R-17 records that a ragged logUp
    argument is exactly the shape that silently changes `num_chunks` and the
    helper degrees. WHERE USED: `degTheta`. -/
def LogupBatchedArgument.lookupWidth {F : Type} (L : LogupBatchedArgument F) : Nat :=
  max L.tableExpressions.size
    (L.inputExpressions.foldl (fun acc inner => max acc inner.size) 0)

/-- How many parallel lookups a batched argument contains.
    rust: plonk/logup.rs:284 (`nb_parallel_lookups`), i.e. the outer length of
    `input_expressions` after the transpose, which is what `.chunks(nb)` splits
    at logup.rs:318. WHERE USED: `degTheta`, `degBeta`, `badPointsBetaCount`. -/
def LogupBatchedArgument.numParallel {F : Type} (L : LogupBatchedArgument F) : Nat :=
  L.inputExpressions.size

/-! ### 2. The challenge schedule (plan 9.4 `Chal`) -/

/-- The verifier's Fiat-Shamir challenges, in transcript order (plan 9.4). Every
    squeeze site, all of them `transcript.squeeze_challenge()`:

    | variant | rust |
    |---|---|
    | `theta` | plonk/verifier.rs:150 |
    | `beta`  | plonk/verifier.rs:167 |
    | `gamma` | plonk/verifier.rs:172 |
    | `trash` | plonk/verifier.rs:194 (`trash_challenge`) |
    | `y`     | plonk/verifier.rs:215 |
    | `x`     | plonk/verifier.rs:304 |
    | `x1`    | poly/kzg/mod.rs:363 (`multi_prepare`) |
    | `x2`    | poly/kzg/mod.rs:364 |
    | `x3`    | poly/kzg/mod.rs:455 |
    | `x4`    | poly/kzg/mod.rs:484 |

    TEN variants, which is all plan 9.4 lists (the work package said eleven; the
    enumeration in 9.4 has ten, and the transcript has no eleventh squeeze).
    The user challenges of the phase loop (plonk/verifier.rs:134) are NOT
    variants: `WellFormed.singlePhase` (plan Section 13, "multi-phase circuits
    are excluded") forces `cs.num_challenges = 0`, so that loop squeezes
    nothing. -/
inductive Chal where
  | theta | beta | gamma | trash | y | x | x1 | x2 | x3 | x4
  deriving BEq

/-- The schedule as a list, so `ksErr` can sum over it. Order is the transcript
    order of `Chal`. -/
def Chal.all : List Chal :=
  [Chal.theta, Chal.beta, Chal.gamma, Chal.trash, Chal.y, Chal.x,
   Chal.x1, Chal.x2, Chal.x3, Chal.x4]

/-! ### 3. `chalMass` and the constant 3 -/

/-- The BLS12-381 scalar order, taken from CompPoly through
    `Midfall.Assumptions.Pairing` (`abbrev r := BLS12_381.scalarFieldSize`,
    CompPoly/Fields/BLS12_381/Basic.lean:22) so the number cannot drift from the
    field the rest of the project uses. -/
def scalarOrder : Nat := Midfall.Assumptions.r

/-- `r` is prime: CompPoly's Pratt certificate
    (CompPoly/Fields/BLS12_381/Basic.lean:27 `ScalarField_is_prime`, `Fact`
    instance at :47). CITED, not reproved: `decide` on `Nat.Prime r` is a
    2^128-step trial division and would blow `maxRecursionDepth`. -/
theorem scalarOrder_prime : Nat.Prime scalarOrder := BLS12_381.ScalarField_is_prime

/-- `r` is a 255-bit prime: `2^254 <= r < 2^255`. This is the size half of what
    CompPoly's own docstring claims for `scalarFieldSize` ("255-bit, 2-adicity
    32", CompPoly/Fields/BLS12_381/Basic.lean:12-14), and what
    `Midfall.Assumptions.pBaseKats_ok` checks as a `Bool`; here it is a theorem,
    by kernel reduction on the literal. -/
theorem scalarOrder_bits : 2 ^ 254 <= scalarOrder ∧ scalarOrder < 2 ^ 255 :=
  ⟨by decide, by decide⟩

/-- The two inequalities that pin the challenge-mass constant: `2r < 2^256 < 3r`.
    Same statement as `Midfall.Security.challenge_mass_constant
    (Security/Challenges.lean:39)`, restated over `scalarOrder` so the ceiling
    lemma below can cite it. Proved by `decide` on `Nat` literals - kernel
    reduction, not `native_decide`, which is confined to Midfall/Instances/. -/
theorem scalarOrder_bracket :
    2 * scalarOrder < 2 ^ 256 ∧ 2 ^ 256 < 3 * scalarOrder :=
  ⟨by decide, by decide⟩

/-- THE CONSTANT 3, JUSTIFIED: `⌈2^256 / r⌉ = 3`, written in the total Nat
    ceiling form `(a + b - 1) / b`. From `2r < 2^256` we get `3r <= 2^256 + r - 1`,
    and from `2^256 < 3r` we get `2^256 + r - 1 < 4r`; `Nat.div_eq_of_lt_le`
    closes it. So a uniform 256-bit digest reduced mod `r` lands on any given
    field element at most `⌈2^256/r⌉ = 3` times out of `2^256`, which is the
    factor design-assessment F2 is about (plan Section 13: "F2 (truncation) is
    handled by `chalMass`"). -/
theorem chal_mass_ceiling : (2 ^ 256 + scalarOrder - 1) / scalarOrder = 3 := by
  have h1 : 2 * scalarOrder < 2 ^ 256 := scalarOrder_bracket.1
  have h2 : 2 ^ 256 < 3 * scalarOrder := scalarOrder_bracket.2
  refine Nat.div_eq_of_lt_le ?_ ?_
  · omega
  · omega

/-- Probability mass of one challenge hitting a bad value when there are `s` bad
    values (plan 9.4 `chalMass`). With `truncated-challenges` the squeezed
    digest is cut to 128 bits (rust: the `truncate` after each
    `squeeze_challenge`, e.g. poly/kzg/mod.rs:456-457), so the denominator is
    `2^128` and there is no reduction-mod-`r` factor at all; otherwise the mass
    is `⌈2^256/r⌉ · s / 2^256 = 3s/2^256` by `chal_mass_ceiling`.
    NONCOMPUTABLE because `ℝ≥0` division is a `Real` division in mathlib - the
    same situation as `Midfall.Security.chalMass`, and outside rule R10, which
    binds the Exec layer. -/
noncomputable def chalMass (F : Features) (s : Nat) : ℝ≥0 :=
  if F.truncatedChallenges then (s : ℝ≥0) / (2 : ℝ≥0) ^ 128
  else 3 * (s : ℝ≥0) / (2 : ℝ≥0) ^ 256

/-! ### 4. The per-round degrees -/

/-- `degTheta idx` - bad points for the logUp column-compression challenge.
    WHERE USED: plan 9.4 `roundErr .theta`.
    rust: plonk/logup.rs:436-438 (`compress_expressions`, the fold
    `acc * theta + eval`) applied to each parallel lookup input vector and to the
    table vector (logup.rs:440-441, :455). Each compressed value is a polynomial
    in `theta` of degree `width - 1`. The helper identity
    `h·∏ⱼ(fⱼ+β) = Σⱼ∏_{k≠j}(f_k+β)` (logup.rs:464-466) multiplies over the `m`
    parallel lookups of one chunk, so its `theta`-degree is at most
    `m·(width-1)`, and summing over the chunks of one argument gives
    `numParallel·(width-1)` because the chunks partition `input_expressions`
    (logup.rs:328). The accumulator identity (logup.rs:471-476) contributes one
    more factor `(t+β)`, i.e. `width-1` more. Summing over arguments is the union
    bound over identities, which is what a round error is.
    CONSERVATIVE, and it needs the paper proof: the count charges every identity
    its full degree, which is sound, but whether a VIOLATED lookup makes the
    polynomial nonzero in `theta` at all (rather than cancelling identically,
    which is what a malicious prover aims for) is a lemma about logUp, not a
    definition. Section 10 owns it. -/
def CircuitIndex.degTheta (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.lookups.foldl (fun acc L =>
    acc + (LogupBatchedArgument.numParallel L + 1) *
        (LogupBatchedArgument.lookupWidth L - 1)) 0

/-- `degBeta idx` - bad points for the permutation/logUp zero-check challenge.
    WHERE USED: plan 9.4 `roundErr .beta`.
    rust, two sources, because `beta` is shared by both arguments:
    * permutation: plonk/permutation.rs:242-277 builds
      `∏ᵢ (vᵢ + β·σᵢ + γ)` and `∏ᵢ (vᵢ + δ^i·β·x + γ)`, one factor linear in `β`
      per column of the chunk, so the grand-product identity has `β`-degree at
      most the number of columns it multiplies over; summed over sets that is at
      most `cs.permutation.columns.size`.
    * logUp: plonk/logup.rs:455 (`compress_expressions(input) + beta`) and
      :473 (`compressed_table + beta`), i.e. one `β` per parallel lookup plus
      one for the table, so `numParallel + 1` per argument.
    CONSERVATIVE in two ways, both deliberate: the permutation term ignores the
    lazy-zip truncation of permutation.rs:236-240 (docs/REVIEW.md R-15), which
    can only REDUCE the number of factors actually multiplied, and the logUp term
    charges the full `numParallel` even though the chunking splits it.
    THIS IS ALSO R-2's third MANIFESTATION: plonk/logup.rs:460 computes
    `product * f.invert().unwrap()`, so any `fⱼ(x) + β = 0` ABORTS the process
    rather than rejecting the proof. That abort set is a subset of the bad set
    counted here - `badPointsBetaCount` makes it explicit - which is what lets
    one side condition discharge all three faces of R-2. -/
def CircuitIndex.degBeta (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.permutation.columns.size +
    idx.cs.lookups.foldl (fun acc L =>
      acc + LogupBatchedArgument.numParallel L + 1) 0

/-- `degGamma idx` - bad points for the permutation offset challenge.
    WHERE USED: plan 9.4 `roundErr .gamma`.
    rust: plonk/permutation.rs:242-277 again - each of the two products is linear
    in `γ` per column, so the identity's `γ`-degree is the number of columns it
    runs over and the sum over sets is at most the number of permutation columns.
    `γ` appears nowhere in logUp or trash (grep `gamma` in plonk/logup.rs and
    plonk/trash.rs returns only `beta`), which is why this is `degBeta` without
    the logUp term. -/
def CircuitIndex.degGamma (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.permutation.columns.size

/-- `degTrash idx` - bad points for the trashcan compression challenge.
    WHERE USED: plan 9.4 `roundErr .trash`.
    rust: plonk/trash.rs:82-87 - the fold
    `fold(F::ZERO, |acc, eval| acc * &trash_challenge + &eval)` over
    `constraint_expressions` is a LEFT fold, so the FIRST constraint carries
    `trash_challenge^(n-1)` (docs/REVIEW.md R-16, third bullet: "the first
    constraint carries the highest power of the trash challenge (Horner)"). The
    identity `compressed - (1 - q)·trash = 0` (trash.rs:87) is therefore a
    polynomial in the challenge of degree `n - 1`, giving `n - 1` bad values per
    trashcan and `Σ_T (|T.constraints| - 1)` overall. An empty trashcan
    contributes 0: its identity is `-(1-q)·trash`, which does not mention the
    challenge at all (Exec/Trash.lean records the same degeneracy). -/
def CircuitIndex.degTrash (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.trashcans.foldl (fun acc T =>
    acc + if T.constraintExpressions.size = 0 then 0
        else T.constraintExpressions.size - 1) 0

/-- Gate identities folded by `y`. rust: plonk/mod.rs:527-549 - one entry per
    `gate.polynomials()` element, in gate order, each paired with the first simple
    selector of its gate (`gate.queried_selectors().iter().filter(is_simple).next()`
    at :543-547, which is what the BTreeMap bucketing of R-19 keys on).
    WHERE USED: `numConstraints`. -/
def CircuitIndex.numGateIdentities (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.gates.foldl (fun acc g => acc + g.polys.size) 0

/-- Permutation identities folded by `y`, reproducing the Rust's four chains and
    its truncations. rust: plonk/permutation.rs:203-281, ported as
    `Permutation.expressions`:
    * `l_0·(1 - z_0)` on the first set only (:206-209) - 1 if there is a set;
    * `(z² - z)·l_last` on the last set only (:212-215) - 1 if there is a set,
      and it comes SECOND (docs/REVIEW.md R-16, second bullet);
    * `l_0·(z_i - z'_{i-1})` for every set but the first (:218-229) - `nsets - 1`;
    * one grand product per zip of sets x column-chunks x eval-chunks
      (:236-240) - the shortest of the three wins (docs/REVIEW.md R-15), which is
      why the `min` of the two chunk counts appears here.
    WHERE USED: `numConstraints`. -/
def CircuitIndex.numPermIdentities (idx : CircuitIndex (Fr p)) : Nat :=
  let nsets := idx.numPermSets
  if nsets = 0 then 0 else 1 + nsets + min nsets idx.numPermEvalChunks

/-- logUp identities folded by `y`. rust: plonk/logup.rs:490-492 -
    `once(boundary).chain(helper_constraints).chain(once(accumulator))`, i.e.
    `num_chunks + 2` per batched argument: the boundary `(l_0 + l_last)·Z(x)`
    (:445) and the accumulator constraint (:471-476).
    WHERE USED: `numConstraints`. -/
def CircuitIndex.numLogupIdentities (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.lookups.foldl (fun acc L =>
      acc + LogupBatchedArgument.numChunksTotal L idx.csDegree + 2) 0

/-- Trash identities folded by `y`: one per trashcan (rust: plonk/trash.rs:87,
    `vec![compressed_expressions - (1 - q) * trash_eval].into_iter()`).
    WHERE USED: `numConstraints`. -/
def CircuitIndex.numTrashIdentities (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.trashcans.size

/-- `numConstraints idx` - the length of the vector
    `partially_evaluate_identities` returns, i.e. how many identities the `y`
    batching folds. WHERE USED: plan 9.4 `roundErr .y`.
    rust: plonk/mod.rs:509-600 builds the vector by chaining gates, permutation,
    lookups and trashcans, and plonk/linearization/verifier.rs:73-79 walks it in
    REVERSE accumulating `y_pow` (`expressions.iter().rev()` at :75), so the
    number of distinct `y` powers used is exactly its length and the batched
    numerator is a polynomial in `y` of degree `length - 1`. Plan 9.4 charges
    `numConstraints` rather than `numConstraints - 1`; that is the conservative
    reading and is what is kept here. docs/REVIEW.md R-19 is the ordering caveat
    this count depends on: the BTreeMap grouping into selector buckets changes
    WHICH identity gets which power (and which fold into `expected_eval`), not
    how many powers are used. -/
def CircuitIndex.numConstraints (idx : CircuitIndex (Fr p)) : Nat :=
  idx.numGateIdentities + idx.numPermIdentities +
    idx.numLogupIdentities + idx.numTrashIdentities

/-- `degX idx` - bad points for the algebraic evaluation challenge `x`.
    WHERE USED: plan 9.4 writes the term inline as
    `idx.cs.degree * idx.n + idx.n`; it is named here so the two halves can be
    attributed separately (see `badPointsX`).
    rust: plonk/verifier.rs:282-288 and poly/domain.rs:39. Each identity has
    degree at most `cs_degree` and is built from column polynomials of degree
    `< n`, so the batched numerator `ν(X)` has degree `< n·cs_degree`; `h(X)` has
    degree `< n·(cs_degree - 1)`, which is exactly
    `domain.quotient_poly_degree = cs_degree - 1` limbs of degree `< n`
    (domain.rs:39, and assessment F7 as Exec/VerifyingKey.lean's
    `domainConsistent` states it), so `ν(X) - h(X)·(X^n - 1)` has degree
    `< n·cs_degree` and contributes at most `n·cs_degree` bad points.
    The `+ n` is R-2's first MANIFESTATION: the `n` domain points themselves,
    where `l_i_range` (poly/domain.rs:463) returns all zeros instead of
    `l_i(x) = 1`. Two different reasons, and the plan's `n·(d+1)` is the sum of
    the two counts. -/
def CircuitIndex.degX (idx : CircuitIndex (Fr p)) : Nat :=
  idx.csDegree * idx.n + idx.n

/-! ### 5. The multi-open point-set structure, read off `constructIntermediateSets` -/

/-- Which polynomial a SHAPE query opens. The real query set
    (plonk/verifier.rs:575-645) is keyed by the commitments themselves, and
    `constructIntermediateSets` groups by `PartialEq` on `CommitmentReference`
    (poly/kzg/utils.rs:55 with query.rs:117-133). At CircuitIndex level there are
    no commitments - the index describes the circuit, not a proof - so the
    IDENTITY of each polynomial is named by which column or argument it is.
    This is the value-equality reading of docs/REVIEW.md R-7, the same one
    Exec/Kzg/MultiOpen instantiates with `kzgCommitBeq`; whether the Rust is
    relying on pointer identity instead is R-7's open question and is flagged in
    this package's report, because it changes the counts below and not just the
    layout. The logUp constructors carry the argument index because each batched
    argument has its own m, its own helpers and its own accumulator
    (plonk/verifier.rs:161, :189, :426), so they must not be merged across
    arguments. The `Linear` commitment of the linearization query
    (plonk/linearization/verifier.rs:110-117) is ONE shape, not a bag of its
    terms: `PartialEq` never compares a `OnePiece` with a `Linear`
    (query.rs:124-131), so the linearization group is disjoint from every
    single-column group, which is what `linearization` encodes. -/
inductive ShapeCom where
  /-- Advice column `i` (plonk/verifier.rs:584-594). -/
  | advice (i : Nat)
  /-- Committed instance column `i` (plonk/verifier.rs:595-608). -/
  | instance_ (i : Nat)
  /-- Fixed column `i` (plonk/verifier.rs:616-628). -/
  | fixed (i : Nat)
  /-- The `i`-th permutation product polynomial
      (plonk/permutation/verifier.rs:155-181). -/
  | permProduct (i : Nat)
  /-- The `i`-th sigma polynomial (plonk/permutation/verifier.rs:185-198). -/
  | sigma (i : Nat)
  /-- The multiplicity polynomial of logUp argument `i`
      (plonk/logup/verifier.rs:180-185). -/
  | logupM (i : Nat)
  /-- Helper polynomial `j` of logUp argument `i`
      (plonk/logup/verifier.rs:187-193). -/
  | logupHelper (i j : Nat)
  /-- The accumulator polynomial of logUp argument `i`
      (plonk/logup/verifier.rs:195-208). -/
  | logupZ (i : Nat)
  /-- The `i`-th trash polynomial (plonk/trash/verifier.rs:65-74). -/
  | trash (i : Nat)
  /-- The linearization polynomial
      (plonk/linearization/verifier.rs:110-117, appended at verifier.rs:646). -/
  | linearization
  deriving BEq

/-- The rotation class of an opening point. The verifier only ever opens at
    `x·ω^r` (plonk/verifier.rs:586, :596, :604, :613 through
    `EvaluationDomain::rotate_omega`, ported as `EvaluationDomain.rotateOmega`,
    plus the three permutation points at permutation/verifier.rs:150-152), and
    for `x ≠ 0` we have `x·ω^r = x·ω^s` iff `r ≡ s [MOD n]`, because `ω` has
    order exactly `n` (poly/domain.rs:64-79). So the class `r mod n` reproduces
    the EQUALITY PATTERN of the real points exactly, which is all
    `constructIntermediateSets` inspects. `WellFormed.nBelowField` keeps the cast
    into `Fr p` injective on classes. -/
def rotationClass (n : Nat) (r : Rotation) : Nat :=
  Int.toNat (r.int % (n : Int))

/-- The verifier's query set as a SHAPE: one entry per opening
    plonk/verifier.rs:575-645 emits, with each point replaced by its rotation
    class and each commitment by its `ShapeCom`. The order follows the Rust's
    `flat_map` chain, because `constructIntermediateSets` numbers points and sets
    by first occurrence (poly/kzg/utils.rs:44-51; the header of
    Exec/Kzg/Utils.lean records that `point_index_map` is first-occurrence
    order), and the set CONTENTS are sorted ascending by `natSort` (utils.rs:162)
    so the order affects the indices, never the three counts derived below.
    Three deliberate choices:
    * the permutation tail uses the i32-truncated rotation
      `-(blinding_factors + 1)` exactly as `Permutation.Evaluated.queries` does
      (permutation/verifier.rs:150-152, docs/REVIEW.md R-9 widened), and the
      `ω^last` openings come in DESCENDING set order with the last set dropped
      (`.enumerate().rev().skip(1)` at :173, docs/REVIEW.md R-16 first bullet).
      An ascending port would change the point-set layout and therefore x1..x4.
    * the instance queries are NOT filtered by
      `column.index() < nb_committed_instances` (verifier.rs:597), because the
      number of committed instances is a config value rather than circuit data.
      Keeping all of them can only add points and sets, which is the conservative
      direction for every count below.
    * fixed queries that are simple selector columns ARE filtered out
      (verifier.rs:622, ported as `ConstraintSystem.hasSimpleSelectorCol`),
      because the verifier never opens them: their evaluation is pinned to 1
      (verifier.rs:400-411, docs/REVIEW.md R-14). -/
def CircuitIndex.queryShapes (idx : CircuitIndex (Fr p)) :
    Array (VerifierQuery (Fr p) ShapeCom) :=
  let n := idx.n
  let pt (r : Rotation) : Fr p := (rotationClass n r : Nat)
  let x := pt Rotation.cur
  let xNext := pt Rotation.next
  -- permutation/verifier.rs:150-152
  let xLast := pt (Rotation.value
    (Permutation.negI32 (Permutation.asI32 (idx.blindingFactors + 1))))
  let q (point : Fr p) (c : ShapeCom) : VerifierQuery (Fr p) ShapeCom :=
    VerifierQuery.new point CommitmentLabel.noLabel c 0
  -- verifier.rs:584-594: advice queries, in `advice_queries` order.
  let adv := idx.cs.adviceQueries.toList.map fun w : Column × Rotation =>
    q (pt w.2) (ShapeCom.advice w.1.index)
  -- verifier.rs:595-608: instance queries (unfiltered, see the header note).
  let inst := idx.cs.instanceQueries.toList.map fun w : Column × Rotation =>
    q (pt w.2) (ShapeCom.instance_ w.1.index)
  -- permutation/verifier.rs:155-170: per set, the openings at x and at ωx.
  let nsets := idx.numPermSets
  let permHead := (List.range nsets).flatMap fun i =>
    [q x (ShapeCom.permProduct i), q xNext (ShapeCom.permProduct i)]
  -- permutation/verifier.rs:172-181: the ω^last openings, descending, last set
  -- dropped (its `last_eval` is None - see `Permutation.Committed.evaluate`).
  let permTail := ((List.range nsets).reverse.drop 1).map fun i =>
    q xLast (ShapeCom.permProduct i)
  -- logup/verifier.rs:180-208: m at x, one helper per chunk at x, then Z at x
  -- and Z at ωx.
  let lks := (List.range idx.cs.lookups.size).zip idx.cs.lookups.toList
  let lookup := lks.flatMap fun w : Nat × LogupBatchedArgument (Fr p) =>
    let helpers := (List.range (LogupBatchedArgument.numChunksTotal w.2 idx.csDegree))
    [q x (ShapeCom.logupM w.1)] ++ (helpers.map fun j => q x (ShapeCom.logupHelper w.1 j)) ++
      [q x (ShapeCom.logupZ w.1), q xNext (ShapeCom.logupZ w.1)]
  -- trash/verifier.rs:65-74: one opening at x per trashcan.
  let trash := (List.range idx.cs.trashcans.size).map fun i => q x (ShapeCom.trash i)
  -- verifier.rs:616-628: fixed queries minus the simple-selector columns.
  let fixed := idx.cs.fixedQueries.toList.filterMap fun w : Column × Rotation =>
    if idx.cs.hasSimpleSelectorCol w.1.index then none
    else some (q (pt w.2) (ShapeCom.fixed w.1.index))
  -- permutation/verifier.rs:185-198: every sigma polynomial at x.
  let sig := (List.range idx.perm.sigmaCommitments.size).map fun i => q x (ShapeCom.sigma i)
  -- verifier.rs:646 (`iter::once(lin_com)`): the linearization at x.
  let lin := [q x ShapeCom.linearization]
  (adv ++ inst ++ permHead ++ permTail ++ lookup ++ trash ++ fixed ++ sig ++ lin).toArray

/-- The point-set structure of the verifier's query set, computed by the ported
    `constructIntermediateSets` (rust: poly/kzg/utils.rs:37-133) rather than
    restated from prose. Plan Section 6 lists "correctness of
    `construct_intermediate_sets`" as a Phase 4 lemma; this is the side of it the
    error budget consumes. -/
def CircuitIndex.shapeSets (idx : CircuitIndex (Fr p)) :
    Except Fault (IntermediateSets (Fr p) ShapeCom) :=
  constructIntermediateSets (F := Fr p) (C := ShapeCom)
    CommitmentReference.beq (idx.queryShapes)

/-- Fallback for the three point-set counts when the shape model produces no
    structure at all. `constructIntermediateSets` fails only with `Error::opening`
    on a duplicated (commitment, point) pair (poly/kzg/utils.rs:55-58), which for
    the shape model means two openings of one polynomial at one rotation class -
    i.e. a constraint system whose rotations collide mod `n`. For any query set,
    `numPointSets <= maxSetSize <= maxPolysPerSet <= #queries`, so `#queries`
    bounds all three and is used verbatim. Under `WellFormed.shapesGroup` the
    fallback is unreachable. -/
def CircuitIndex.shapeQueryCount (idx : CircuitIndex (Fr p)) : Nat :=
  idx.queryShapes.size

/-- `numPointSets idx` - the number of distinct point-index sets
    (rust: poly/kzg/utils.rs:20-30, the `point_idx_sets` BTreeMap whose length
    becomes `point_sets.len()` at poly/kzg/mod.rs:371-374).
    WHERE USED: plan 9.4 `roundErr .x2` and `roundErr .x4`.
    For `x2`: the batched polynomial is `Σᵢ x2^i·(q_i(X) - r_i(X))/I_i(X)`, built
    by the reversed fold `acc_eval * x2 + eval` at poly/kzg/mod.rs:466-476, so
    its `x2`-degree is `numPointSets - 1` and the bad count is `numPointSets`.
    For `x4`: the combination is `Σᵢ x4^i·q_com_i + x4^{numPointSets}·f_com` with
    `let size = q_coms.len() + 1` (poly/kzg/mod.rs:489-505, and the same `size`
    drives the eval side at :508-517), i.e. `numPointSets + 1` powers - which is
    why plan 9.4 writes `numPointSets + 1` for `.x4` and plain `numPointSets`
    for `.x2`. -/
def CircuitIndex.numPointSets (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.shapeSets with
  | .ok (_, sets) => sets.size
  | .error _ => idx.shapeQueryCount

/-- `maxSetSize idx` - the largest number of points in one point set
    (rust: the `point_sets[i].len()` that is the sort key at
    poly/kzg/mod.rs:418-420 and the number of factors of `den` at :478).
    WHERE USED: plan 9.4 `roundErr .x3`, as `maxSetSize * idx.n`. See
    `badPointsX3Count` below: that product is the shape of the degree bound, but
    it does not obviously cover the denominator zeros, which is R-2's second
    manifestation. -/
def CircuitIndex.maxSetSize (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.shapeSets with
  | .ok (_, sets) => sets.foldl (fun acc s => max acc s.size) 0
  | .error _ => idx.shapeQueryCount

/-- `maxPolysPerSet idx` - the largest number of commitments sharing one point
    set. rust: poly/kzg/mod.rs:390
    (`let nb_x1_powers = q_coms.iter().map(|v| v.len()).max().unwrap_or(0)`),
    which is exactly how many `x1` powers the batcher takes at :394-397, and the
    assert at :391 says the eval side never exceeds it.
    WHERE USED: plan 9.4 `roundErr .x1`. The batched polynomial for one set is
    `Σⱼ x1^j·(Cⱼ - eⱼ)` (poly/kzg/mod.rs:386, :399-401), a polynomial in `x1` of
    degree at most `(#commitments in that set) - 1`, so the worst set gives
    `maxPolysPerSet` bad values of `x1`. -/
def CircuitIndex.maxPolysPerSet (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.shapeSets with
  | .ok (cmap, sets) =>
      (List.range sets.size).foldl (fun acc i =>
        max acc (cmap.toList.filter (fun cd => cd.setIndex == i)).length) 0
  | .error _ => idx.shapeQueryCount

/-- `verifierQueries idx` - how many random-oracle queries the verifier itself
    makes, which plan 9.4 adds to the adversary's `qH` in the chain-collision
    term of `ksErr` (and in S4's `(qH + V)²/2^256`).
    rust: the transcript is `CircuitTranscript<Keccak256>`
    (transcript/implementors.rs:194-212, ported as Exec/Transcript.lean): an
    absorb is `update`, i.e. byte concatenation with NO permutation, and a
    squeeze is one `keccak256` of the accumulated buffer followed by a reseed.
    So the verifier's RO queries are exactly its squeezes: the six in
    plonk/verifier.rs (:150, :167, :172, :194, :215, :304), the four in
    `multi_prepare` (poly/kzg/mod.rs:363, :364, :455, :484), and one per user
    challenge in the phase loop (plonk/verifier.rs:134), of which
    `cs.num_challenges` many exist - zero under `WellFormed.singlePhase`.
    NOT JUSTIFIED FROM THE RUST, and flagged: if the ROM model charges a query
    per ABSORBED ITEM rather than per squeeze, this must be replaced by the
    number of transcript elements, which is not a function of `idx` alone - the
    instance values are absorbed (verifier.rs:94-101) and their length is
    caller-controlled. See this package's report. -/
def CircuitIndex.verifierQueries (idx : CircuitIndex (Fr p)) : Nat :=
  10 + idx.cs.numChallenges

/-- `srsBound idx` - the SRS size the statements assume.
    WHERE USED: plan 9.4 S1's `hN : idx.srsBound ≤ N`.
    rust: poly/domain.rs:47-50 sizes the extended domain as the smallest
    `2^{extended_k} >= n·quotient_poly_degree` and :53 asserts
    `extended_k <= F::S`; the quotient numerator lives there, so it is the
    largest degree any polynomial in the argument can reach. Every honest
    COMMITMENT has degree `< n` (advice, fixed, sigma, products, helpers,
    quotient limbs, the linearization, and the multi-open combination at
    poly/kzg/mod.rs:489-505), so `n` would do for the verifier's own checks;
    `2^{extended_k}` is the conservative choice because an AGM adversary holding
    `N` group elements can commit to anything of degree `< N` and the reduction
    has to reason about polynomials as large as the extended domain.
    NOT JUSTIFIED FROM THE RUST as a minimum: which of `n`,
    `n·(cs_degree-1)`, `2^{extended_k}` or `n·(cs_degree+1)` S1 actually needs is
    a paper-proof question (Section 10). Flagged in the report. -/
def CircuitIndex.srsBound (idx : CircuitIndex (Fr p)) : Nat :=
  nextPowerOfTwo (idx.n * (idx.csDegree - 1))

/-! ### 6. The bad-point sets R-2 asks for -/

/-- R-2 manifestation 1, as a decidable predicate: the domain itself. At any
    `x = ω^i`, `l_i_range` (poly/domain.rs:448-473, ported as
    `EvaluationDomain.lIRange`) returns ALL ZEROS rather than `l_i(x) = 1`,
    because `batch_invert` skips the zero denominator *and* `x^n - 1 = 0` makes
    the `common` factor vanish (Exec/Domain.lean records exactly this at its
    `lIRange` doc). In a field the `n`-th roots of unity are exactly the domain
    (the domain is the full order-`n` subgroup, poly/domain.rs:64-79), so
    `x^n = 1` IS the bad set, and its size is `idx.n` - the `+ idx.n` half of
    `degX`. WHERE USED: the `x` row of plan 9.4. -/
def CircuitIndex.badPointsX (idx : CircuitIndex (Fr p)) (x : Fr p) : Bool :=
  x ^ idx.n == 1

/-- The point sets concatenated, WITH MULTIPLICITY: the points where `multi_prepare`
    (`let den = points.iter().fold(ONE, |acc, point| acc * &(x3 - point))` and
    then `den.invert().unwrap()`, poly/kzg/mod.rs:478-479) ABORTS the process
    instead of rejecting the proof. R-2 manifestation 2. Computable from the
    shape model up to the unknown `x`: the entries are rotation classes, and the
    real points are `x·ω^r`. A point belonging to two sets appears twice, so this
    is an over-count of the union; `dedup`-ing it is not needed because the bound
    below is only ever used as an upper bound. WHERE USED: `badPointsX3Count`. -/
def CircuitIndex.badPointsX3 (idx : CircuitIndex (Fr p)) : List (Fr p) :=
  match idx.shapeSets with
  | .ok (_, sets) => sets.toList.flatMap fun s => s.toList
  | .error _ => []

/-- The size of R-2 manifestation 2's bad set, counted WITH MULTIPLICITY over the
    sets. Distinct point sets may overlap - `{0}` and `{0,1}` are two different sets
    sharing a point, and utils.rs:163 dedups only on the whole sorted list - so this
    over-counts the union, which is the conservative direction for a bad-point
    bound. The union's true size is `(badPointsX3 idx).dedup.length`. -/
def CircuitIndex.badPointsX3Denominator (idx : CircuitIndex (Fr p)) : Nat :=
  match idx.shapeSets with
  | .ok (_, sets) => sets.foldl (fun acc s => acc + s.size) 0
  | .error _ => idx.shapeQueryCount

/-- The honest `x3` bad-point count: the roots of the combined polynomial (at
    most `n`, because every `q_i` and the `f` built by the Kate divisions at
    poly/kzg/mod.rs:264-276 has degree `< n`) PLUS the denominator zeros of
    `badPointsX3Denominator`, which are a CRASH set rather than a rejection set
    and so have to be excluded separately.
    PLAN 9.4 DOES NOT USE THIS: it writes `maxSetSize * idx.n` for `.x3`.
    `roundErr` follows the plan verbatim rather than silently improving on it
    (plan Section 12: never weaken - or here, never re-derive - a statement
    quietly), and this definition is the counter-example that Phase 4 has to
    reconcile. See the package report. -/
def CircuitIndex.badPointsX3Count (idx : CircuitIndex (Fr p)) : Nat :=
  idx.n + idx.badPointsX3Denominator

/-- R-2 manifestation 3, counted: how many factors `fⱼ(x) + β` the inverse at
    plonk/logup.rs:460 (`product * f.invert().unwrap()`) takes - one per
    parallel lookup per argument (the `partial_products` map at :458-461 runs
    over the chunk and the chunks partition `input_expressions`). This is a
    SUBSET of the `beta`-bad set bounded by `degBeta`, which is what lets one
    side condition discharge all three faces of R-2. -/
def CircuitIndex.badPointsBetaCount (idx : CircuitIndex (Fr p)) : Nat :=
  idx.cs.lookups.foldl (fun acc L => acc + LogupBatchedArgument.numParallel L) 0

/-! ### 7. `roundErr` and `ksErr` -/

/-- The §9.4 degree bundle, as PARAMETERS. Plan 9.4's `roundErr (F idx)` reads as
    if the degrees were functions of the index alone; making them an explicit
    record keeps the shape of 9.4 while letting Phase 4 pass sharper degrees (for
    instance `badPointsX3Count` in place of `maxSetSize * n`) without touching
    the definitions here. `CircuitIndex.degrees` is the bundle this file
    computes. -/
structure Degrees where
  /-- `roundErr .theta` input: `CircuitIndex.degTheta`. -/
  degTheta : Nat
  /-- `roundErr .beta` input: `CircuitIndex.degBeta`. -/
  degBeta : Nat
  /-- `roundErr .gamma` input: `CircuitIndex.degGamma`. -/
  degGamma : Nat
  /-- `roundErr .trash` input: `CircuitIndex.degTrash`. -/
  degTrash : Nat
  /-- `roundErr .y` input: `CircuitIndex.numConstraints`. -/
  numConstraints : Nat
  /-- `roundErr .x` input: `CircuitIndex.degX = cs_degree·n + n`. -/
  degX : Nat
  /-- `roundErr .x1` input: `CircuitIndex.maxPolysPerSet`. -/
  maxPolysPerSet : Nat
  /-- `roundErr .x2` input: `CircuitIndex.numPointSets`. -/
  numPointSets : Nat
  /-- `roundErr .x3` input: `CircuitIndex.maxSetSize`, multiplied by `n`. -/
  maxSetSize : Nat
  /-- The domain size, used by the `.x3` row. -/
  n : Nat
  /-- `roundErr .x4` input is `numPointSets + 1`; this field is the `V` of the
      chain-collision term. -/
  verifierQueries : Nat

/-- The degrees of this constraint system, as the bundle `roundErr` consumes. -/
def CircuitIndex.degrees (idx : CircuitIndex (Fr p)) : Degrees :=
  { degTheta := idx.degTheta
    degBeta := idx.degBeta
    degGamma := idx.degGamma
    degTrash := idx.degTrash
    numConstraints := idx.numConstraints
    degX := idx.degX
    maxPolysPerSet := idx.maxPolysPerSet
    numPointSets := idx.numPointSets
    maxSetSize := idx.maxSetSize
    n := idx.n
    verifierQueries := idx.verifierQueries }

/-- Per-round error mass, plan 9.4 verbatim: each challenge's bad-point count
    pushed through `chalMass`. The `.x` row is `degX = cs_degree·n + n` and the
    `.x3` row is `maxSetSize·n`, both exactly as the plan writes them. -/
noncomputable def roundErrDegrees (F : Features) (d : Degrees) : Chal → ℝ≥0
  | .theta => chalMass F d.degTheta
  | .beta => chalMass F d.degBeta
  | .gamma => chalMass F d.degGamma
  | .trash => chalMass F d.degTrash
  | .y => chalMass F d.numConstraints
  | .x => chalMass F d.degX
  | .x1 => chalMass F d.maxPolysPerSet
  | .x2 => chalMass F d.numPointSets
  | .x3 => chalMass F (d.maxSetSize * d.n)
  | .x4 => chalMass F (d.numPointSets + 1)

/-- Plan 9.4's `roundErr (F idx)`, i.e. `roundErrDegrees` at the degrees this
    file computes. -/
noncomputable def roundErr (F : Features) (idx : CircuitIndex (Fr p)) :
    Chal → ℝ≥0 := roundErrDegrees F idx.degrees

/-- The whole budget as a list, in transcript order - the `∑ c` of plan 9.4. -/
noncomputable def roundErrAll (F : Features) (d : Degrees) : List ℝ≥0 :=
  Chal.all.map (roundErrDegrees F d)

/-- The knowledge-soundness error of the native verifier, plan 9.4's `ksErr`:
    `(qH + 1)·Σ_c roundErr(c) + (qH + V)²/2^256`. The first term is the union
    bound over rounds, with `qH + 1` because the reduction rewinds the transcript
    once per adversary query plus the honest run; the second is the Keccak-chain
    collision term of S4, where `V = verifierQueries`. NO PROBABILISTIC CONTENT
    is claimed by this definition - it is the shape S1 will be stated against. -/
noncomputable def ksErrDegrees (F : Features) (d : Degrees) (qH : Nat) : ℝ≥0 :=
  ((qH + 1 : Nat) : ℝ≥0) * (roundErrAll F d).sum +
    (((qH + d.verifierQueries : Nat) ^ 2 : Nat) : ℝ≥0) / (2 : ℝ≥0) ^ 256

/-- Plan 9.4's `ksErr (F idx qH)`. -/
noncomputable def ksErr (F : Features) (idx : CircuitIndex (Fr p)) (qH : Nat) :
    ℝ≥0 := ksErrDegrees F idx.degrees qH

/-! ### 8. `WellFormed` at the circuit-index level -/

/-- The side conditions plan 9.4 attaches to S1 (`hwf : idx.WellFormed .solidity`)
    and S2. These are the hypotheses the DEFINITIONS above silently rely on: each
    one names the line that would otherwise make a count wrong rather than merely
    large. Exec/VerifyingKey.lean's `VerifyingKey.WellFormed` is the same shape at
    the VK level and the two are complementary, not duplicated - a
    `CircuitIndex` has no domain, no commitments and no `csDegree` cache.

  * `csDegreeOk` / `blindingFactorsOk` - the two `Except`-valued ported
    functions the degrees read; their `error` arms are the R-13 logUp panics.
  * `chunkLenPositive` - `numPermSets` divides by `cs_degree - 2`
    (permutation/verifier.rs:41) and `divCeil a 0 = 0` would silently report zero
    permutation identities.
  * `singlePhase` - plan Section 13; it is what makes `Chal` have ten variants
    and `verifierQueries` have no user challenges.
  * `committedInstancesOn` / `fewerPointSetsOff` - the shape model reproduces the
    query list of the production feature set. With `fewer-point-sets` on,
    `compute_dummy_queries` (poly/kzg/utils.rs:135-187) pads the multi-point sets
    into one, which changes `numPointSets` and `maxSetSize`; the direction of
    that change is not obvious, so the flag is required OFF rather than assumed
    harmless.
  * `nBelowField` - `rotationClass` casts a class into `Fr p`, injective on
    `[0, n)` only when `n <= p`.
  * `lookupRectangular` - `lookupWidth` and `numChunksTotal` mean "the width" and
    "the chunk count" only for a transposed, non-ragged argument
    (logup.rs:286-296; R-17 records that a ragged one silently changes the
    degrees).
  * `sigmaCountMatches` - the three-way zip of permutation.rs:236-240 truncates,
    so `numPermIdentities` is the true identity count only when the sigma vector
    has as many entries as there are permutation columns.
  * `shapesGroup` - the shape model must not hit `DuplicatedQuery`, i.e. no two
    openings of one polynomial at one rotation class.
  * `usableNonempty` - plan 9.3 quantifies the relation over `idx.usable`, the
    domain minus the blinding region (`blinding_factors + 3` rows,
    circuit.rs:2517-2524); if that is empty the relation is vacuously true and
    extraction has nothing to say. -/
structure CircuitIndex.WellFormed (idx : CircuitIndex (Fr p)) (F : Features) : Prop where
  csDegreeOk : idx.cs.degree = .ok idx.csDegree
  blindingFactorsOk : idx.cs.blindingFactors = .ok idx.blindingFactors
  chunkLenPositive : 3 ≤ idx.csDegree
  singlePhase : idx.cs.numChallenges = 0
  committedInstancesOn : F.committedInstances = true
  fewerPointSetsOff : F.outerFewerPointSets = false
  nBelowField : idx.n ≤ p
  lookupRectangular : ∀ L ∈ idx.cs.lookups, 1 ≤ L.inputExpressions.size ∧
    1 ≤ L.tableExpressions.size ∧
    ∀ inner ∈ L.inputExpressions, inner.size == L.tableExpressions.size
  sigmaCountMatches : idx.perm.sigmaCommitments.size == idx.cs.permutation.columns.size
  shapesGroup : (idx.shapeSets).toOption.isSome
  usableNonempty : idx.blindingFactors + 3 < idx.n

/-! ### 9. Known-answer checks -/

-- Hand-computed checks on one synthetic constraint system, in the style of
-- Exec/Circuit.lean and Exec/Domain.lean: each expectation is derived in the
-- docstring of `katCs` from the halo2 book and the Rust lines cited above, and
-- each is a `Bool` so it is evaluated by the kernel rather than proved. NOT
-- wired into scripts/checks.sh, per the work package.

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A constraint system sized so that every number below can be checked by hand:
    `Fr 17`, `k = 4` so `n = 16` (and `n ≤ p`, as `WellFormed` demands); 2 advice
    columns each queried at `cur` and `next`; ONE gate whose single polynomial is
    `a₀·a₁·a₀`, degree 3; ONE batched logUp argument with 3 parallel lookups of
    width 2 over a 2-expression table, all inputs degree 1 and a constant
    selector; 2 permutation columns and 2 sigma commitments, so `chunk_len = 1`
    gives 2 sets; 1 trashcan with 2 constraints.
    The hand computation, line by line:
    * `cs_degree = 3`: the permutation constant 3 dominates the gate (3) and the
      trashcan (2); the logUp argument asks for 3 too, because
      `max_degree = next_power_of_two(3-1)+1 = 3`, `lookup_degree = 1`,
      `nb = (3-1)/1 = 2`, helper degree `2·1+1 = 3`, accumulator degree
      `2 + 0 + 1 = 3`, and `(max 3 3 - 1).next_power_of_two() + 1 = 3`
      (logup.rs:224-269).
    * `blinding_factors = 9`: `max(3, max num_advice_queries = 2) = 3`, +1
      trashcan = 4, +2 chunks = 6, +1+1+1 = 9 (circuit.rs:2474-2508).
    * `numPermSets = divCeil 2 (3-2) = 2`, and likewise on the sigma side.
    * `degTheta = (3+1)·(2-1) = 4`; `degBeta = 2 + (3+1) = 6`;
      `degGamma = 2`; `degTrash = 2-1 = 1`.
    * `numConstraints = 1 (gate) + 5 (perm: 1 + 2 + min 2 2) + 4 (logup: 2
      chunks + 2) + 1 (trash) = 11`.
    * `degX = 3·16 + 16 = 64`; `verifierQueries = 10`;
      `srsBound = next_power_of_two(16·2) = 32`.
    * point sets: rotation classes are 0 (x), 1 (ωx) and `-10 mod 16 = 6`
      (ω^{-(bf+1)}x). Set {0,1} holds advice a₀, advice a₁, the second
      permutation product and the logUp accumulator: 4 commitments. Set {0,1,6}
      holds the first permutation product only: 1. Set {0} holds m, two helpers,
      the trash polynomial, two fixed columns, two sigmas and the linearization:
      9. So `numPointSets = 3`, `maxSetSize = 3`, `maxPolysPerSet = 9`. -/
def katAdvice0 : Column := { index := 0, columnType := Any.advice Advice.default }
def katAdvice1 : Column := { index := 1, columnType := Any.advice Advice.default }
def katFixed0 : Column := { index := 0, columnType := Any.fixed }
def katFixed1 : Column := { index := 1, columnType := Any.fixed }
def katE0 : Expression (Fr 17) := katAdvice0.queryCell Rotation.cur
def katE1 : Expression (Fr 17) := katAdvice1.queryCell Rotation.cur
def katEn0 : Expression (Fr 17) := katAdvice0.queryCell Rotation.next
def katEn1 : Expression (Fr 17) := katAdvice1.queryCell Rotation.next
def katTab0 : Expression (Fr 17) :=
  Expression.fixed { index := some 0, columnIndex := 0, rotation := Rotation.cur }
def katTab1 : Expression (Fr 17) :=
  Expression.fixed { index := some 1, columnIndex := 1, rotation := Rotation.cur }

/-- The one gate: a single degree-3 polynomial. -/
def katGate : Gate (Fr 17) :=
  { name := "mul", constraintNames := #["c"],
    polys := #[Expression.product (Expression.product katE0 katE1) katE0],
    queriedSelectors := #[], queriedCells := #[] }

/-- The one batched logUp argument: 3 parallel lookups of width 2 over a
    2-expression table, every input of degree 1, constant selector. -/
def katLookup : LogupBatchedArgument (Fr 17) :=
  { name := "l", selector := Expression.constant 1,
    inputExpressions := #[#[katE0, katE1], #[katE1, katE0], #[katEn0, katEn1]],
    tableExpressions := #[katTab0, katTab1] }

/-- The one trashcan, with 2 constraints. -/
def katTrash : TrashArgument (Fr 17) :=
  { name := "t", selector := Expression.constant 1,
    constraintExpressions := #[Expression.product katE0 katE1, katE1] }

def katCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default (F := Fr 17) with
    numFixedColumns := 2,
    numAdviceColumns := 2,
    numInstanceColumns := 0,
    numSelectors := 0,
    numChallenges := 0,
    adviceColumnPhase := #[{ val := 0 }, { val := 0 }],
    gates := #[katGate],
    adviceQueries := #[(katAdvice0, Rotation.cur), (katAdvice0, Rotation.next),
                       (katAdvice1, Rotation.cur), (katAdvice1, Rotation.next)],
    numAdviceQueries := #[2, 2],
    instanceQueries := #[],
    fixedQueries := #[(katFixed0, Rotation.cur), (katFixed1, Rotation.cur)],
    permutation := { columns := #[katAdvice0, katAdvice1] },
    lookups := #[katLookup],
    trashcans := #[katTrash] }

/-- The features value with truncation OFF, so both branches of `chalMass` are
    exercised. -/
def katFullFeatures : Features :=
  { committedInstances := true, truncatedChallenges := false,
    outerFewerPointSets := false, outerSingleHCommitment := false }

def katPerm : PermutationAssembly katCs 4 :=
  { cycles := #[],
    sigmaCommitments := #[katFixed0, katFixed1] }

/-- The matching circuit index. The permutation has no cycles because these KATs
    are about degrees, not about the relation; the sigma count matches the column
    count, which is `WellFormed.sigmaCountMatches`. -/
def katIdx : CircuitIndex (Fr 17) :=
  { cs := katCs,
    k := 4,
    fixed := fun _ _ => 0,
    perm := katPerm,
    repr := 0 }

/-- The degrees, each equal to the hand computation in `katCs` above. -/
def degrees_kats_ok : Bool :=
  katIdx.csDegree == 3 &&
  katIdx.blindingFactors == 9 &&
  katIdx.n == 16 &&
  katIdx.numPermSets == 2 &&
  katIdx.numPermEvalChunks == 2 &&
  katIdx.degTheta == 4 &&
  katIdx.degBeta == 6 &&
  katIdx.degGamma == 2 &&
  katIdx.degTrash == 1 &&
  katIdx.numGateIdentities == 1 &&
  katIdx.numPermIdentities == 5 &&
  katIdx.numLogupIdentities == 4 &&
  katIdx.numTrashIdentities == 1 &&
  katIdx.numConstraints == 11 &&
  katIdx.degX == 64 &&
  katIdx.verifierQueries == 10 &&
  katIdx.srsBound == 32

/-- The logUp chunk arithmetic, through the ported function rather than a
    restatement: `nb_parallel_lookups_per_chunk = 2`, so 3 parallel lookups give
    `divCeil 3 2 = 2` chunks, width 2, and the helper degree `2·1+1 = 3` is what
    keeps `cs_degree` at 3. -/
def logup_kats_ok : Bool :=
  LogupBatchedArgument.numChunksTotal katLookup 3 == 2 &&
  (match katLookup.numChunks 3 with | .ok n => n == 2 | .error _ => false) &&
  LogupBatchedArgument.lookupWidth katLookup == 2 &&
  LogupBatchedArgument.numParallel katLookup == 3 &&
  (match katLookup.degreeBatchedArgument 3 with
   | .ok d => d == 3 | .error _ => false) &&
  (match katCs.degree with | .ok d => d == 3 | .error _ => false) &&
  (match katCs.blindingFactors with | .ok b => b == 9 | .error _ => false)

/-- The point-set structure, as the hand computation gives it. Note `x1 = 9 >
    x2 = 3` and `x1 > x4 = 4`: the batching error is dominated by how many
    polynomials share a point, not by how many points there are - the qualitative
    prediction the halo2 book makes about the multi-open, reproduced here from
    `constructIntermediateSets` itself rather than from prose. -/
def pointSet_kats_ok : Bool :=
  katIdx.queryShapes.size == 20 &&
  katIdx.numPointSets == 3 &&
  katIdx.maxSetSize == 3 &&
  katIdx.maxPolysPerSet == 9 &&
  katIdx.badPointsX3Denominator == 6 &&
  katIdx.badPointsX3Count == 22 &&
  katIdx.degrees.maxSetSize * katIdx.degrees.n == 48 &&
  katIdx.badPointsBetaCount == 3 &&
  katIdx.badPointsX3.length == 6 &&
  (match katIdx.shapeSets with | .ok (_, sets) => sets.size == 3 | .error _ => false)

/-- R-2 manifestation 1, checked as a set rather than as prose: in `Fr 17` the 16
    nonzero elements are exactly the 16th roots of unity, so `badPointsX` flags
    all of them and not 0. That is the `+ idx.n` half of `degX`. -/
def badPointsX_kats_ok : Bool :=
  ((List.range 17).filter fun v => katIdx.badPointsX (v : Fr 17)).length == 16 &&
  katIdx.badPointsX 0 == false &&
  katIdx.badPointsX 1 == true &&
  katIdx.badPointsX 3 == true

/-- The bundle wiring: `CircuitIndex.degrees` agrees with the individual
    definitions, field for field, and `Chal` has the ten variants plan 9.4 lists.
    (`roundErr` itself lands in `ℝ≥0`, which is noncomputable, so it is not checked
    here - the inputs it consumes are, and its body is one `chalMass` per row.) -/
def roundErr_kats_ok : Bool :=
  let d := katIdx.degrees
  d.degTheta == 4 && d.degBeta == 6 && d.degGamma == 2 && d.degTrash == 1 &&
  d.numConstraints == 11 && d.degX == 64 && d.maxPolysPerSet == 9 &&
  d.numPointSets == 3 && d.maxSetSize == 3 && d.n == 16 && d.verifierQueries == 10 &&
  Chal.all.length == 10

/-- The arithmetic behind the constant 3, as a `Bool` mirror of the theorems
    `scalarOrder_bits` and `scalarOrder_bracket`; `chal_mass_ceiling` is the
    conclusion (`⌈2^256/r⌉ = 3`) and is a theorem, not a check. -/
def chalMass_kats_ok : Bool :=
  scalarOrder < 2 ^ 255 && scalarOrder ≥ 2 ^ 254 &&
  2 * scalarOrder < 2 ^ 256 && 2 ^ 256 < 3 * scalarOrder

/-- The KAT index really satisfies the side conditions, so the numbers above are
    evidence and not accident. Each conjunct is the decidable form of the matching
    field of `CircuitIndex.WellFormed`. -/
def wellFormed_kats_ok : Bool :=
  (match katIdx.cs.degree with | .ok 3 => true | _ => false) &&
  (match katIdx.cs.blindingFactors with | .ok 9 => true | _ => false) &&
  katIdx.csDegree ≥ 3 &&
  katIdx.cs.numChallenges == 0 &&
  Features.solidity.committedInstances &&
  ! Features.solidity.outerFewerPointSets &&
  katIdx.n ≤ 17 &&
  (katCs.lookups.toList.all fun L => 1 ≤ L.inputExpressions.size &&
    1 ≤ L.tableExpressions.size &&
    (L.inputExpressions.toList.all fun inner =>
      inner.size == L.tableExpressions.size)) &&
  katIdx.perm.sigmaCommitments.size == katIdx.cs.permutation.columns.size &&
  (match katIdx.shapeSets with | .ok _ => true | .error _ => false) &&
  katIdx.blindingFactors + 3 < katIdx.n

end Kats

end Midfall.Halo2.Spec

#eval Midfall.Halo2.Spec.degrees_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.logup_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.pointSet_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.badPointsX_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.roundErr_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.chalMass_kats_ok   -- expect true
#eval Midfall.Halo2.Spec.wellFormed_kats_ok   -- expect true

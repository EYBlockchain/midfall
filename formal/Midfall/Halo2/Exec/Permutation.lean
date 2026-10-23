-- |
-- Midfall.Halo2.Exec.Permutation
--
-- Plan Section 4 module map, row `plonk/permutation/*, logup/*, trash/*,
-- linearization/verifier.rs -> Exec/{Permutation,Logup,Trash}`: the verifier
-- path of the permutation argument. Sources:
-- proofs/src/plonk/permutation/verifier.rs (198 lines, all of it) and the
-- verifier-reachable parts of proofs/src/plonk/permutation.rs (282 lines).
--
-- Port rules: R1 provenance on every def, R2 names, R3 iterator semantics
-- (`zip` truncates to the shorter input, `chunks` yields `ceil(len/k)` slices,
-- `rev().skip(1)` reverses *before* dropping), R4 panics become `Fault.panic`,
-- R5 `Nat`/`Int` with the one lossy `as i32` cast emulated at its site, R6
-- `Vec` -> `Array`, R7 exponentiation through `Exec/Arith.powVartime`, R9 the
-- transcript reads go through the `Hashable` record, R10 total and computable.
--
-- REACHABILITY. The set grepped is the one the plan names: plonk/verifier.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, plonk/mod.rs,
-- poly/** and proofs/solidity-verifier/src. Ported, with the site that reaches
-- each:
--   permutation::verifier::Committed        plonk/verifier.rs:179 (what
--                                           read_product_commitments returns), :223
--   permutation::verifier::CommonEvaluated  plonk/verifier.rs:414, :485, :645
--   permutation::verifier::Evaluated        plonk/verifier.rs:418, :482, :624
--   permutation::Evaluated                  plonk/verifier.rs:482 (`.sets`),
--                                           plonk/mod.rs:493, :554
--   permutation::VerifyingKey               plonk/mod.rs:64 (the VK field),
--                                           :261-266, :298, :332;
--                                           plonk/verifier.rs:414, :645
--   Argument::read_product_commitments      plonk/verifier.rs:179
--   VerifyingKey::evaluate                  plonk/verifier.rs:414
--   Committed::evaluate                     plonk/verifier.rs:418
--   Evaluated::queries                      plonk/verifier.rs:624
--   CommonEvaluated::queries                plonk/verifier.rs:645
--   permutation::expressions                plonk/mod.rs:553
--                                           (`partially_evaluate_identities`)
-- NOT verifier-reachable, so skipped with the evidence at each site below:
-- `Argument::{new, add_column, get_columns}`, `Argument::required_degree` (it
-- lives in Exec/Circuit as `PermutationArgument.requiredDegree`), the
-- `VerifyingKey` serde plumbing (`read`, `write`, `bytes_length`) and everything
-- under `ProvingKey`.
--
-- TWO STRUCTURAL CHOICES, both forced, both recorded.
--
-- 1. THE TYPES LIVE IN A `Permutation` NAMESPACE. The Rust calls this module's
--    verifying key `permutation::VerifyingKey`; `plonk::VerifyingKey` - the one
--    Exec/VerifyingKey owns - is a different type with the same name, and Lean has
--    no module path to separate them. So the permutation VK and its three state
--    types live in `Midfall.Halo2.Permutation`, which is also how the plan spells
--    the LogUp and trash verifier paths.
-- 2. THE VERIFIER FUNCTIONS TAKE THE VK'S PARTS, NOT THE VK. `plonk::VerifyingKey`
--    is a boundary file for this package, so where the Rust reads `vk.domain`,
--    `vk.cs.blinding_factors()`, `vk.cs_degree` or `vk.cs.permutation` the port
--    takes those as parameters, and each site says which. Exec/Verifier passes
--    them from the real VK; nothing else changes.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript

namespace Midfall.Halo2

/-- A cell of the trace: (column, row). -/
structure Cell where
  column : Column
  row : Nat

/-- rust: proofs/src/plonk/permutation/keygen.rs Assembly, verifier view. The
    sigma polynomials are given as their cycle decomposition here, because that
    is the form the relation quantifies over (plan 9.3 perm.cycles). -/
structure PermutationAssembly {F : Type} (cs : ConstraintSystem F) (k : Nat) where
  /-- Equivalence classes of cells under the copy constraints: each cycle is a
      list of cells that must carry equal values. -/
  cycles : Array (Array Cell)
  /-- sigma mappings, as the verifier reads them from the VK commitments. -/
  sigmaCommitments : Array Column

namespace Permutation

/-- rust: proofs/src/plonk/permutation/verifier.rs:12-15 (`struct Committed<F,
    CS> { permutation_product_commitments: Vec<CS::Commitment> }`).

    The Rust carries `F` too, but only through the
    `CS: PolynomialCommitmentScheme<F>` parameter - no field has type `F`. The
    port drops that phantom and keeps the commitment type, which under the KZG
    instantiation (plan 9.1) is `G₁`. -/
structure Committed (G₁ : Type) where
  permutationProductCommitments : Array G₁

/-- rust: proofs/src/plonk/permutation/verifier.rs:17-19 (`struct
    CommonEvaluated<F> { permutation_evals: Vec<F> }`). This is what
    plonk/verifier.rs:414 binds to `permutations_common`. -/
structure CommonEvaluated (F : Type) where
  permutationEvals : Array F

/-- rust: proofs/src/plonk/permutation.rs:179-184 (`struct Evaluated<F>`), the
    three openings of one permutation product polynomial.

    FORCED R2 DEVIATION, recorded: the Rust has two types called `Evaluated` on
    this path - `permutation::Evaluated` (here) and
    `permutation::verifier::Evaluated` (below) - and Lean has no module path to
    separate them. The verifier's keeps the bare name, because that is the type
    the verifier trace stores; this one is named for the field it is collected
    into (`sets`). -/
structure SetEvaluated (F : Type) where
  permutationProductEval : F
  permutationProductNextEval : F
  /-- `None` for the last set only - see `Committed.evaluate`, which is the only
      way the reference builds one. -/
  permutationProductLastEval : Option F

/-- rust: proofs/src/plonk/permutation/verifier.rs:21-24 (`struct Evaluated<F,
    CS> { coms: Committed<F, CS>, sets: Vec<permutation::Evaluated<F>> }`). The
    `coms` field is private in Rust and read only by `queries` (:161, :167,
    :177); it is a field here because the port has no `impl` blocks to hide it
    behind. -/
structure Evaluated (F G₁ : Type) where
  coms : Committed G₁
  sets : Array (SetEvaluated F)

/-- rust: proofs/src/plonk/permutation.rs:93-97 (`struct VerifyingKey<F, CS> {
    commitments: Vec<CS::Commitment> }`), the sigma commitments of one
    permutation argument - one per *column*, not per set. Reached as the
    `permutation` field of `plonk::VerifyingKey` (plonk/mod.rs:64) and read by
    `VerifyingKey.evaluate` and `CommonEvaluated.queries`. -/
structure VerifyingKey (G₁ : Type) where
  commitments : Array G₁

/-- `Vec[i]` in Rust, where an out-of-bounds index is a panic (rule R4). Lean's
    `xs[i]` panics too, which rule R10 does not allow in Exec, so every indexed
    read on this path goes through here and reports the Rust site. -/
def atIndex {α : Type} (xs : Array α) (i : Nat) (site : String) : Except Fault α :=
  match xs[i]? with
  | some x => .ok x
  | none => .error (Fault.panic site)

/-- rust: the `usize as i32` cast inside `Rotation(-((blinding_factors + 1) as
    i32))` at permutation/verifier.rs:152. A Rust `as` cast from `usize` to
    `i32` keeps the low 32 bits and reinterprets them signed: it is neither
    saturating nor lossless - `2^31` becomes `-2^31`, and `2^32 + 5` becomes
    `5`. `Nat` cannot express that, so the truncation is emulated (rule R5:
    emulated where it can actually occur, and `blinding_factors` is a sum of
    caller-supplied counts, so it can). This is docs/REVIEW.md R-9. -/
def wrapI32 (x : Int) : Int :=
  let m := x % 4294967296
  if m < 2147483648 then m else m - 4294967296

/-- rust: the same cast, applied to a `usize`. -/
def asI32 (n : Nat) : Int := wrapI32 (Int.ofNat n)

/-- rust: the unary `-` at permutation/verifier.rs:152. Negating `i32::MIN`
    overflows: the reference release profile (BASELINE.md) wraps it back to
    `i32::MIN`; a debug build panics. The port follows the release reading, which
    is again a wrap of the mathematical negation. -/
def negI32 (x : Int) : Int := wrapI32 (-x)

/-- `Vec::chunks(k).count()`, i.e. `ceil(len / k)` for `k > 0`. `chunks(0)`
    panics in Rust; every caller here checks the divisor first. -/
def numChunksOf (len chunkLen : Nat) : Nat := divCeil len chunkLen

/-- `slice::chunks(k)[i]`: the i-th chunk, truncated to whatever is left. -/
def chunkOf {α : Type} (xs : Array α) (i chunkLen : Nat) : List α :=
  (xs.toList.drop (i * chunkLen)).take chunkLen

/-- rust: proofs/src/plonk/permutation/verifier.rs:27-61
    (`Argument::read_product_commitments`), called at plonk/verifier.rs:179.

    `chunk_len = vk.cs_degree - 2` (:41) is a `usize` subtraction and
    `Vec::chunks` panics on a zero chunk length (:45). Neither can fire for a
    constraint system the Rust built: `ConstraintSystem::degree` is at least
    `permutation::Argument::required_degree`, the constant 3 at permutation.rs:78,
    so `chunk_len >= 1`. A hand-built one - which is exactly what the conformance
    exporter feeds us - can have `cs_degree` 1 or 2, and then the reference
    panics, so the panic is kept as a `Fault` (rule R4). `cs_degree = 1` diverges
    further: in the release profile `1 - 2` wraps to `usize::MAX` and yields one
    chunk per non-empty column list, where `Nat` saturates to 0 and the port
    reports the `chunks(0)` panic. Recorded, not emulated (rule R5).

    `.map(|_| transcript.read())` at :46 discards the chunk contents: the
    verifier reads one product commitment per *chunk of columns*, not one per
    column. That is the entire reason `chunk_len` is `cs_degree - 2`. -/
def readProductCommitments {G₁ : Type} (perm : PermutationArgument) (csDegree : Nat)
    (h : Hashable G₁) : TranscriptM (Committed G₁) := do
  -- verifier.rs:41
  let chunkLen := csDegree - 2
  -- verifier.rs:45
  unless chunkLen > 0 do
    throw (Fault.panic "proofs/src/plonk/permutation/verifier.rs:45")
  -- verifier.rs:43-47
  let n := numChunksOf perm.columns.size chunkLen
  let permutationProductCommitments ← tmReadN h n
  return { permutationProductCommitments }

/-- rust: proofs/src/plonk/permutation/verifier.rs:64-90
    (`permutation::VerifyingKey::evaluate`) - the call plonk/verifier.rs:414
    binds to `permutations_common`.

    One scalar is read per *commitment in the VK*: the number of sigma
    polynomials fixes how many permutation evaluations at `x` the proof carries.
    The Rust reads them as `F` (inferred from `CommonEvaluated<F>`); here that is
    `Fr p`, which is why this def is generic in `p` while the type it reads from is
    generic only in the commitment type. -/
def VerifyingKey.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey G₁) : TranscriptM (CommonEvaluated (Fr p)) := do
  let permutationEvals ← tmReadN hashableFr vk.commitments.size
  return { permutationEvals }

/-- rust: proofs/src/plonk/permutation/verifier.rs:93-141 (`Committed::evaluate`),
    called at plonk/verifier.rs:418.

    The loop is the part worth reading twice. `while iter.next().is_some()` walks
    an iterator over the product commitments and *discards* each element, so it
    runs exactly `k` times, and `iter.len() > 0` at :121 is the count *after* that
    advance. So the third eval is read for every set except the last, and the last
    set's `permutation_product_last_eval` is `None` - which is what makes the two
    `unwrap()`s downstream (verifier.rs:178 and permutation.rs:225) unreachable for
    anything this function built. Total reads: `3k - 2` for `k >= 1`, and `0` for
    `k = 0` (the loop body never runs, so an argument with no product commitments
    contributes no evals at all). -/
def Committed.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (coms : Committed G₁) : TranscriptM (Evaluated (Fr p) G₁) := do
  let k := coms.permutationProductCommitments.size
  let mut sets : Array (SetEvaluated (Fr p)) := #[]
  for i in List.range k do
    -- verifier.rs:109
    let permutationProductEval ← tmRead hashableFr
    -- verifier.rs:115
    let permutationProductNextEval ← tmRead hashableFr
    -- verifier.rs:121-131: `iter.len()` is `k - i - 1` once `next()` has run
    let permutationProductLastEval ←
      if i < k - 1 then do
        let e ← tmRead hashableFr
        pure (some e)
      else
        pure none
    sets := sets.push { permutationProductEval, permutationProductNextEval,
                        permutationProductLastEval }
  return { coms, sets }

/-- rust: proofs/src/plonk/permutation/verifier.rs:144-182 (`Evaluated::queries`),
    reached at plonk/verifier.rs:624.

    The Rust reads two things off `vk`: `vk.cs.blinding_factors()` (:150) and
    `vk.domain` (:151-152). Both are parameters here - header, choice 2. Note
    that `blinding_factors` is already a `Nat`: `ConstraintSystem.blindingFactors`
    in Exec/Circuit is the def that carries the `i32::MAX` panic at
    circuit.rs:2510, and this def does not repeat it.

    docs/REVIEW.md R-9 bites at :152: the rotation is
    `-((blinding_factors + 1) as i32)`, built from caller-controlled data through
    a truncating cast and then negated with wrapping negation, so a constraint
    system with `blinding_factors + 1 >= 2^31` opens the product at a *positive*
    rotation. `rotate_omega` does not panic on it; it computes a `2^31`-power of
    `omega_inv`. Any `Supported`-style bound on rotations has to cite this site as
    well as verifier.rs:361.

    The order is the Rust chain order and it is not the index order: the
    `omega^last`-point queries come from `.enumerate().rev().skip(1)` (:173),
    which reverses *before* dropping, so the indices are `k-2, k-3, ..., 0` -
    descending, and never the last set (whose `last_eval` is `None`). -/
def Evaluated.queries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (ev : Evaluated (Fr p) G₁) (domain : EvaluationDomain (Fr p))
    (blindingFactors : Nat) (x : Fr p) :
    Except Fault (Array (VerifierQuery (Fr p) G₁)) := do
  -- verifier.rs:150-152
  let xNext := domain.rotateOmega x Rotation.next
  let xLast := domain.rotateOmega x
    (Rotation.value (negI32 (asI32 (blindingFactors + 1))))
  let coms := ev.coms.permutationProductCommitments
  -- verifier.rs:155-170: per set, in order, the opening at x and the opening at
  -- omega*x, both against the same product commitment.
  let head ← (List.zip (List.range ev.sets.size) ev.sets.toList).mapM fun (i, set) => do
    let c ← atIndex coms i "proofs/src/plonk/permutation/verifier.rs:161"
    let c' ← atIndex coms i "proofs/src/plonk/permutation/verifier.rs:167"
    return [ VerifierQuery.new x CommitmentLabel.noLabel c set.permutationProductEval,
             VerifierQuery.new xNext CommitmentLabel.noLabel c' set.permutationProductNextEval ]
  -- verifier.rs:172-181
  let tail ← ((List.range ev.sets.size).reverse.drop 1).mapM fun i => do
    let set ← atIndex ev.sets i "proofs/src/plonk/permutation/verifier.rs:173"
    let c ← atIndex coms i "proofs/src/plonk/permutation/verifier.rs:177"
    match set.permutationProductLastEval with
    | none => .error (Fault.panic "proofs/src/plonk/permutation/verifier.rs:178")
    | some e => return [VerifierQuery.new xLast CommitmentLabel.noLabel c e]
  return ((List.flatten head).toArray ++ (List.flatten tail).toArray)

/-- rust: proofs/src/plonk/permutation/verifier.rs:185-198
    (`CommonEvaluated::queries`), reached at plonk/verifier.rs:645 - the only
    place the sigma commitments are opened, each labelled
    `CommitmentLabel::Permutation(i)`.

    `vkey.commitments.iter().zip(self.permutation_evals.iter())` truncates to the
    shorter input (rule R3), so a VK carrying more sigma commitments than the
    proof has evaluations for contributes no query for the extras rather than
    failing. The two are equal in length for anything `VerifyingKey::evaluate`
    produced, which is the only way the reference builds a `CommonEvaluated`. -/
def CommonEvaluated.queries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (common : CommonEvaluated (Fr p)) (vkey : VerifyingKey G₁) (x : Fr p) :
    Array (VerifierQuery (Fr p) G₁) :=
  let pairs := List.zip vkey.commitments.toList common.permutationEvals.toList
  ((List.zip (List.range pairs.length) pairs).map
    fun (i, (commitment, eval)) =>
      VerifierQuery.new x (CommitmentLabel.permutation i) commitment eval).toArray

/-- rust: proofs/src/plonk/permutation.rs:244-253 and :264-273 - the same
    `match column.column_type()` closure body, written twice in the Rust.

    `get_any_query_index` panics for a query the constraint system never collected
    (circuit.rs:2074, :2084, :2094, ported in Exec/Circuit) and the following
    slice index panics when the index is past the end of the evaluation vector;
    both are `Fault.panic` sites (rule R4). The site string names the permutation.rs
    line, which is where the Rust would report it from. -/
def columnEval {p : ℕ} [Fact (Nat.Prime p)] (cs : ConstraintSystem (Fr p)) (col : Column)
    (adviceEvals fixedEvals instanceEvals : Array (Fr p)) :
    Except Fault (Fr p) := do
  let idx ← cs.getAnyQueryIndex col Rotation.cur
  match col.columnType with
  | .advice _ => atIndex adviceEvals idx "proofs/src/plonk/permutation.rs:246"
  | .fixed => atIndex fixedEvals idx "proofs/src/plonk/permutation.rs:249"
  | .instance => atIndex instanceEvals idx "proofs/src/plonk/permutation.rs:252"

/-- rust: proofs/src/plonk/permutation.rs:187-282 (`permutation::expressions`),
    the grand-product identities, reached from `partially_evaluate_identities` at
    plonk/mod.rs:553.

    The Rust takes `vk` and `p` - and `p` is `&vk.cs.permutation`, the same object
    twice - and reads `vk.cs_degree`, `vk.cs.permutation` and
    `vk.cs.get_any_query_index`. The port takes the constraint system and
    `cs_degree` (header, choice 2).

    `delta` is `F::DELTA` (:262, :276), the generator of the `t`-order
    multiplicative subgroup (`ff::PrimeField::DELTA`, ff-0.13.1/src/lib.rs:350).
    `Exec/Arith.FieldConsts` carries `zeta` but not `delta`, and Exec/Arith is a
    boundary file for this package, so the constant is a parameter here. Owner:
    Exec/Arith or Assumptions/ should grow the field; until then every caller has
    to supply it, which is the point of making it explicit rather than hiding it.

    FOUR chains, in the Rust's order - and the order is load-bearing, because it
    is the order the quotient numerator is batched in and the contract's QVM
    program is generated from the same sequence:
      1. `l_0 * (1 - z_0)` on the first set only (:206-209)
      2. `l_last * (z_l^2 - z_l)` on the last set only (:212-215)
      3. `l_0 * (z_i - z'_{i-1}(omega^last))` for every set but the first (:218-229)
      4. the per-set grand product (:235-281)
    Note that 1 and 2 come *before* 3: a one-set argument emits
    `[l_0*(1-z), (z^2-z)*l_last, grand]`, not `[l_0*(1-z), grand, ...]`.

    Two laziness details that change the observable behaviour (rule R3):
      * the left product is built from
        `columns.iter().map(..).zip(permutation_evals.iter())` (:242-258), so
        `get_any_query_index` runs for at most `min(columns, permutation_evals)`
        columns. Mapping the column list first would turn a panic the reference
        never reaches into one the port does, so the port zips first and looks up
        afterwards.
      * `current_delta` starts at `beta * x * delta^(chunk_index * chunk_len)` and
        is multiplied by `delta` *after* each factor (:261-276), so the i-th column
        of the chunk uses `delta^(chunk_index * chunk_len + i)`.

    And one truncation that is not a panic: the outer
    `sets.zip(columns.chunks).zip(permutation_evals.chunks).enumerate()` (:236-240)
    stops at the shortest of the three, so a mismatch between the number of sets,
    the number of column chunks and the number of permutation-eval chunks silently
    drops whole identities rather than failing. -/
def expressions {p : ℕ} [Fact (Nat.Prime p)]
    (cs : ConstraintSystem (Fr p)) (csDegree : Nat)
    (sets : Array (SetEvaluated (Fr p))) (common : CommonEvaluated (Fr p))
    (adviceEvals fixedEvals instanceEvals : Array (Fr p))
    (l0 lLast lBlind beta gamma x delta : Fr p) :
    Except Fault (Array (Fr p)) := do
  -- permutation.rs:202
  let chunkLen := csDegree - 2
  -- permutation.rs:237 (`p.columns.chunks(chunk_len)`)
  unless chunkLen > 0 do
    throw (Fault.panic "proofs/src/plonk/permutation.rs:237")
  let columns := cs.permutation.columns
  -- permutation.rs:206-209
  let first := match sets[0]? with
    | some s => [l0 * (1 - s.permutationProductEval)]
    | none => []
  -- permutation.rs:212-215
  let last := match sets.toList.reverse.head? with
    | some s =>
        [((s.permutationProductEval * s.permutationProductEval) - s.permutationProductEval) * lLast]
    | none => []
  -- permutation.rs:218-229: `skip(1).zip(iter)` pairs z_{i+1} with z_i, so the
  -- `unwrap()` at :225 is on the *previous* set's last eval.
  let middle ← (List.zip (sets.toList.drop 1) sets.toList).mapM fun (set, lastSet) =>
    match lastSet.permutationProductLastEval with
    | none => .error (Fault.panic "proofs/src/plonk/permutation.rs:225")
    | some prevLast => .ok ((set.permutationProductEval - prevLast) * l0)
  -- permutation.rs:235-281
  let n := min sets.size (min (numChunksOf columns.size chunkLen)
                              (numChunksOf common.permutationEvals.size chunkLen))
  let products ← (List.range n).mapM fun chunkIndex => do
    let set ← atIndex sets chunkIndex "proofs/src/plonk/permutation.rs:240"
    let cols := chunkOf columns chunkIndex chunkLen
    let permEvals := chunkOf common.permutationEvals chunkIndex chunkLen
    -- the left product: zip first, look up second (see the doc note above)
    let mut left := set.permutationProductNextEval
    for (col, permEval) in List.zip cols permEvals do
      let eval ← columnEval cs col adviceEvals fixedEvals instanceEvals
      left := left * (eval + beta * permEval + gamma)
    -- the right product: every column of the chunk, with the delta ladder
    let mut right := set.permutationProductEval
    let mut currentDelta := (beta * x) * powVartime delta (chunkIndex * chunkLen)
    for col in cols do
      let eval ← columnEval cs col adviceEvals fixedEvals instanceEvals
      right := right * (eval + currentDelta + gamma)
      currentDelta := currentDelta * delta
    return (left - right) * (1 - (lLast + lBlind))
  return (first ++ last ++ middle ++ products).toArray

/-! rust: proofs/src/plonk/permutation.rs:38-41 (`Argument::new`) and :81-85
    (`Argument::add_column`) - NOT verifier-reachable. Evidence: the only call
    sites are plonk/circuit.rs:1825 (`ConstraintSystem::new`) and
    plonk/circuit.rs:1889 (`ConstraintSystem::permute`), i.e. circuit
    construction, which plan Section 1 puts out of scope (the VK is imported from
    Rust). Both are already recorded in Exec/Circuit.lean, which owns the
    argument struct; `Argument::get_columns` (:88-90) is reached only from
    plonk/dev/mod.rs:1064, :1089 and plonk/dev/cost_model.rs:370 - the dev
    tooling, not the verifier - and is ported there as
    `PermutationArgument.getColumns` for the generator's protocol module. -/

/-! rust: proofs/src/plonk/permutation.rs:105-113 (`VerifyingKey::write`),
    :115-127 (`VerifyingKey::read`) and :128-134 (`bytes_length`) - NOT
    verifier-reachable, and the one item on the brief's list that is skipped
    rather than ported. Evidence: the only call sites are plonk/mod.rs:105
    (`plonk::VerifyingKey::write`), plonk/mod.rs:185
    (`plonk::VerifyingKey::read_from_cs`) and plonk/mod.rs:220
    (`plonk::VerifyingKey::bytes_length`) - the VK's own binary serde. Nothing in
    plonk/verifier.rs, plonk/{permutation,logup,trash,linearization}/verifier.rs,
    poly/** or proofs/solidity-verifier/src reaches them: the generator takes the
    VK as a value, and plan Section 1 imports the VK (`vk.json`) rather than
    parsing its bytes. They are also not portable as written - all three are
    generic over `SerdeFormat` and `CS::Commitment: ProcessedSerdeObject`, the
    midnight_curves binary point encoding, which the port models as `G1Codec`
    (design decision D-P6) with no `SerdeFormat` switch. If Exec/VerifyingKey
    decides to read a VK from bytes it owns that codec choice; this module
    deliberately does not pre-empt it. -/

/-! rust: the `#[cfg(feature = "solidity-verifier-trace")]` blocks in
    permutation/verifier.rs - NOT ported, in any of the three modules that read this Rust.
    Evidence: the feature is `proofs/Cargo.toml:117`
    (`solidity-verifier-trace = []`), it is not one of the four flags
    `Exec/Features.lean` carries under rule R8, and every block is a call to
    `plonk::solidity_trace::record_*` -
    pure logging of a value the surrounding code already has, into a module that
    the plan's Section 4 module map does not list and plan Section 1 puts out of
    scope ("trace and gas-checkpoint render modes"). Dropping them changes no
    value, no error class and no transcript byte: the absorbs happen inside
    `transcript.read()`, not in the trace hooks. The conformance harness (plan
    Section 5) reads the trace on the Rust side instead of asking the port to
    reproduce it. -/

/-! rust: proofs/src/plonk/permutation.rs:137-178 (`ProvingKey` and its `read`,
    `write`, `bytes_length`) and the whole of permutation/{prover,keygen}.rs -
    NOT verifier-reachable: prover and keygen code, out of scope by plan
    Section 1. `compute_polys_and_cosets` is reached only from plonk/mod.rs:426
    (`ProvingKey::read`) and permutation/keygen.rs. -/

/-! ## Known-answer checks

    Hand-computed over `Fr 17`, in the style of Exec/Circuit.lean. The commitment
    type is instantiated at `Nat` with `hashableU32` so the transcript reads are 4
    bytes wide and the checks stay executable without a curve; the scalar reads
    use the real `hashableFr`. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Seven fixed columns - the column list is only counted, never inspected, by
    `read_product_commitments`. -/
def permCols (n : Nat) : PermutationArgument :=
  { columns := ((List.range n).map fun i =>
      { index := i, columnType := Any.fixed }).toArray }

/-- `n` bytes-wide little-endian scalars concatenated, as a proof buffer. -/
def bytesOf (vals : List Nat) (w : Nat) : Bytes :=
  vals.foldl (fun acc v => ByteArray.append acc (natToBytesLE v w)) Bytes.empty

/-- A constraint system with one registered fixed query, column 0 at `cur`, and
    one permutation column: the smallest shape `expressions` can evaluate. -/
def permKatCs : ConstraintSystem (Fr 17) :=
  { ConstraintSystem.default with
    numFixedColumns := 1
    fixedQueries := #[({ index := 0, columnType := Any.fixed }, Rotation.cur)]
    permutation := permCols 1 }

/-- `read_product_commitments` reads one commitment per *chunk*, not per column:
    7 columns at `cs_degree` 5 is `ceil(7/3) = 3` reads, and the 12-byte buffer is
    exactly consumed. At `cs_degree` 3 the chunk length is 1, so 7 reads are needed
    and a 12-byte buffer runs out (`UnexpectedEof`). At `cs_degree` 2 the chunk
    length is 0 and the reference panics in `Vec::chunks`. -/
def readProductCommitments_kats_ok : Bool :=
  let buf := bytesOf [1, 2, 3] 4
  match (readProductCommitments (permCols 7) 5 hashableU32).run
      (Transcript.initFromBytes buf) with
  | .ok (c, t) =>
      c.permutationProductCommitments.toList == [1, 2, 3] && t.pos == 12 &&
      (match (readProductCommitments (permCols 7) 3 hashableU32).run
          (Transcript.initFromBytes buf) with
       | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
       | _ => false) &&
      (match (readProductCommitments (permCols 7) 2 hashableU32).run
          (Transcript.initFromBytes buf) with
       | .error (Fault.panic "proofs/src/plonk/permutation/verifier.rs:45") => true
       | _ => false)
  | .error _ => false

/-- `Committed::evaluate` reads `3k - 2` scalars: for `k = 2`, five of them, and
    the *last* set is the one whose `last_eval` is `None`. With `k = 0` it reads
    nothing at all. -/
def committedEvaluate_kats_ok : Bool :=
  let coms : Committed Nat := { permutationProductCommitments := #[10, 20] }
  match (coms.evaluate (p := 17)).run
      (Transcript.initFromBytes (bytesOf [1, 2, 3, 4, 5] 32)) with
  | .ok (ev, t) =>
      ev.sets.size == 2 && t.pos == 5 * 32 &&
      (ev.sets.map fun s => s.permutationProductEval.val) == #[1, 4] &&
      (ev.sets.map fun s => s.permutationProductNextEval.val) == #[2, 5] &&
      (ev.sets.map fun s => (s.permutationProductLastEval.map fun v => v.val)).toList
        == [some 3, none] &&
      (match (({ permutationProductCommitments := #[] } : Committed Nat)).evaluate
          (p := 17) |>.run (Transcript.initFromBytes Bytes.empty) with
       | .ok (e, t') => e.sets.size == 0 && t'.pos == 0
       | .error _ => false)
  | .error _ => false

/-- `Evaluated.queries` on two sets: four queries at `x` and `omega*x`, then the
    single `omega^last` query for set 0 only - descending, and never the last set.
    Over the `ZMod 17` domain (`omega = 13`, `omega_inv = 4`) with `x = 5`:
    `x_next = 5*13 = 14`, and with `blinding_factors = 1` the rotation is `-2`, so
    `x_last = 5*4^2 = 80 = 12`. -/
def queries_kats_ok : Bool :=
  let sets : Array (SetEvaluated (Fr 17)) :=
    #[ { permutationProductEval := 1, permutationProductNextEval := 2,
         permutationProductLastEval := some 3 },
       { permutationProductEval := 4, permutationProductNextEval := 5,
         permutationProductLastEval := none } ]
  let ev : Evaluated (Fr 17) Nat :=
    { coms := { permutationProductCommitments := #[10, 20] }, sets }
  match EvaluationDomain.new (F := Fr 17) fc17 1 2 with
  | .error _ => false
  | .ok d => match ev.queries (p := 17) d 1 5 with
    | .error _ => false
    | .ok qs =>
        qs.size == 5 &&
        (qs.map fun q => q.point.val) == #[5, 14, 5, 14, 12] &&
        (qs.map fun q => q.eval.val) == #[1, 2, 4, 5, 3] &&
        (qs.map fun q => match q.commitment with
          | .onePiece c => c
          | .linear _ _ _ => 0).toList == [10, 10, 20, 20, 10] &&
        (qs.map fun q => match q.commitmentLabel with
          | .noLabel => true
          | _ => false).all id &&
        -- a third set whose `last_eval` is `None` reaches the unwrap at :178.
        -- The tail walks the sets in *descending* index order, so set 1 - the
        -- middle one, whose last_eval is None - is what trips it. The commitment
        -- vector has to grow too, or the head loop trips the index check at :161
        -- first, which is itself worth knowing.
        (match ({ coms := { permutationProductCommitments := #[10, 20, 30] },
                  sets := sets.push { permutationProductEval := 6,
                                      permutationProductNextEval := 7,
                                      permutationProductLastEval := none } }
                : Evaluated (Fr 17) Nat).queries (p := 17) d 1 5 with
         | .error (Fault.panic "proofs/src/plonk/permutation/verifier.rs:178") => true
         | _ => false) &&
        -- Two sets but three commitments: nothing trips, because the loop walks
        -- the *sets* and simply never reaches coms[2]. The extra commitment is
        -- dropped silently - the mirror image of the truncation above.
        (match ({ coms := { permutationProductCommitments := #[10, 20, 30] },
                  sets } : Evaluated (Fr 17) Nat).queries (p := 17) d 1 5 with
         | .ok qs => qs.size == 5
         | .error _ => false)

/-- R-9: the rotation is built through `as i32` and a wrapping negation, so
    `blinding_factors + 1 = 2^31` - which a `usize` holds without trouble - comes
    out as `+2^31` negated and wrapped, i.e. `-2^31` again, and `2^32 + 5` reads
    as `5`. -/
def asI32_kats_ok : Bool :=
  asI32 5 == 5 && asI32 2147483647 == 2147483647 &&
  asI32 2147483648 == -2147483648 && asI32 4294967296 == 0 &&
  asI32 4294967301 == 5 && negI32 (-2147483648) == -2147483648 &&
  negI32 5 == -5 && negI32 2147483647 == -2147483647

/-- `CommonEvaluated.queries`: one query per (commitment, eval) pair, labelled
    `Permutation(i)`, and the zip truncates - three commitments with two evals
    gives two queries, not three. -/
def commonQueries_kats_ok : Bool :=
  let common : CommonEvaluated (Fr 17) := { permutationEvals := #[7, 8] }
  let vkey : VerifyingKey Nat := { commitments := #[100, 200, 300] }
  let qs := common.queries (p := 17) vkey 13
  qs.size == 2 &&
  (qs.map fun q => match q.commitmentLabel with
    | .permutation 0 => true
    | .permutation 1 => true
    | _ => false).all id &&
  (qs.map fun q => q.eval.val) == #[7, 8] &&
  (qs.map fun q => q.point.val) == #[13, 13] &&
  (qs.map fun q => match q.commitment with
    | .onePiece c => c
    | .linear _ _ _ => 0) == #[100, 200]

/-- One fixed column, one set, one permutation eval, over `Fr 17`:
    `chunk_len = 5 - 2 = 3`, so the single column chunk holds the one column.
      1. `l_0 * (1 - z)` = `2 * (1 - 2)` = `-2` = `15`
      2. `(z^2 - z) * l_last` = `(4 - 2) * 5` = `10`
      3. no cross-set term (one set)
      4. left  = `z_next * (f + beta*s + gamma)` = `3 * (9 + 35 + 11)` = `3 * 55`;
         `55 = 4 mod 17`, so `12`
         right = `z * (f + beta*x*delta^0 + gamma)`; `beta*x = 65 = 14`, so the
         factor is `9 + 14 + 11 = 34 = 0` and right is `0`
         `(left - right) * (1 - (l_last + l_blind))` = `12 * (1 - 12)` =
         `12 * 6` = `72` = `4`
    and the emitted order is `[1, 2, 4]` - the last-set constraint comes second. -/
def expressions_kats_ok : Bool :=
  let sets : Array (SetEvaluated (Fr 17)) :=
    #[{ permutationProductEval := 2, permutationProductNextEval := 3,
        permutationProductLastEval := none }]
  let common : CommonEvaluated (Fr 17) := { permutationEvals := #[7] }
  match expressions (p := 17) permKatCs 5 sets common #[] #[9] #[] 2 5 7 5 11 13 3 with
  | .error _ => false
  | .ok out => out.map (fun v => v.val) == #[15, 10, 4]

/-- The right-hand loop sees every column of the chunk, including one that was
    never registered as a query, so it reaches the `get_any_query_index` panic -
    while the left-hand loop, which zips first, does not. Reversing the two loops'
    laziness is the mistake this pins. -/
def expressionsLazy_kats_ok : Bool :=
  let cs := { permKatCs with
    permutation := { columns := #[{ index := 0, columnType := Any.fixed },
                                  { index := 5, columnType := Any.fixed }] } }
  let sets : Array (SetEvaluated (Fr 17)) :=
    #[{ permutationProductEval := 2, permutationProductNextEval := 3,
        permutationProductLastEval := none }]
  let common : CommonEvaluated (Fr 17) := { permutationEvals := #[7] }
  match expressions (p := 17) cs 5 sets common #[] #[9] #[] 2 5 7 5 11 13 3 with
  | .error (Fault.panic "proofs/src/plonk/circuit.rs:2084") => true
  | _ => false

end Kats

#eval readProductCommitments_kats_ok   -- expect true
#eval committedEvaluate_kats_ok        -- expect true
#eval queries_kats_ok                  -- expect true
#eval asI32_kats_ok                    -- expect true
#eval commonQueries_kats_ok            -- expect true
#eval expressions_kats_ok              -- expect true
#eval expressionsLazy_kats_ok          -- expect true

end Permutation

end Midfall.Halo2

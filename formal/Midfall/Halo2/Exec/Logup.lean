-- |
-- Midfall.Halo2.Logup
--
-- Plan Section 4 module map, row `plonk/permutation/*, logup/*, trash/*,
-- linearization/verifier.rs -> Exec/{Permutation,Logup,Trash}`: the verifier
-- path of the LogUp lookup argument. Sources:
-- proofs/src/plonk/logup/verifier.rs (212 lines, all of it) and the
-- verifier-reachable parts of proofs/src/plonk/logup.rs (483 lines).
--
-- The argument records themselves - LogupBatchedArgument, its three degree
-- helpers, LogupChunkedArgument and chunkByDegree - live in Exec/Circuit.lean,
-- because ConstraintSystem.lookups names them and Lean has no mutually
-- recursive modules (see that file's header, choice 3). This module adds only
-- the verifier path: the four transcript-reading state types, the three reads,
-- the queries and the two identities. Nothing is redefined here.
--
-- Port rules: R1 provenance, R2 names, R3 iterator semantics (`zip` truncates,
-- `fold` is a left fold), R4 panics become `Fault.panic`, R6 `Vec` -> `Array`,
-- R7 `invert` returns `Option`, so `f.invert().unwrap()` is an explicit panic
-- site, R9 the transcript reads go through the `Hashable` record, R10 total.
--
-- REACHABILITY. The set grepped is the one the plan names: plonk/verifier.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, plonk/mod.rs,
-- poly/** and proofs/solidity-verifier/src. Ported, with the site that reaches
-- each:
--   logup::verifier::CommittedMultiplicities  plonk/verifier.rs:155-164, :183
--   logup::verifier::Committed                plonk/verifier.rs:183-192, :221
--   logup::verifier::Evaluated                plonk/verifier.rs:421-429, :483,
--                                             :625
--   logup::Evaluated                          plonk/verifier.rs:483
--                                             (`.evaluated`), plonk/mod.rs:494
--   ChunkedArgument::read_multiplicities       plonk/verifier.rs:161
--   CommittedMultiplicities::read_commitment   plonk/verifier.rs:189
--   Committed::evaluate                        plonk/verifier.rs:426
--   Evaluated::queries                         plonk/verifier.rs:625
--   Evaluated::expressions                     plonk/mod.rs:574
--                                              (`partially_evaluate_identities`)
-- NOT verifier-reachable, so skipped with the evidence at each site below:
-- `BatchedArgument::new` (circuit construction), the two `Debug` impls, and the
-- `selector_expression` / `table_expressions` accessors.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Domain
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript

namespace Midfall.Halo2
namespace Logup

/-- rust: proofs/src/plonk/logup/verifier.rs:29-32 (`struct
    CommittedMultiplicities<F, CS> { multiplicities: CS::Commitment }`), the
    shared m(X) commitment, read after `theta` is squeezed and before `beta` is.
    As in Exec/Permutation, the Rust's `F` parameter is a phantom - it appears
    only in `CS: PolynomialCommitmentScheme<F>` - so the port keeps only the
    commitment type. -/
structure CommittedMultiplicities (G₁ : Type) where
  multiplicities : G₁

/-- rust: proofs/src/plonk/logup/verifier.rs:34-43 (`struct Committed<F, CS> {
    multiplicities, helper_polys: Vec<CS::Commitment>, accumulator }`). One
    shared m and Z plus one h_i per chunk - which is why the number of helper
    commitments is `nb_chunks` and not one per lookup: the chunking happened
    before this read (plonk/verifier.rs:189 passes `batch.num_chunks()`). -/
structure Committed (G₁ : Type) where
  multiplicities : G₁
  helperPolys : Array G₁
  accumulator : G₁

/-- rust: proofs/src/plonk/logup.rs:374-380 (`struct Evaluated<F>`), the LogUp
    polynomial evaluations at x (and Z at omega*x).

    FORCED R2 DEVIATION, recorded: the Rust has two types called `Evaluated` on
    this path - `logup::Evaluated` (here) and `logup::verifier::Evaluated`
    (below) - and Lean has no module path to separate them. The verifier's keeps
    the bare name, because that is the type the verifier trace stores; this one
    is named for what it holds. -/
structure Evals (F : Type) where
  multiplicitiesEval : F
  helperEvals : Array F
  accumulatorEval : F
  accumulatorNextEval : F

/-- rust: proofs/src/plonk/logup/verifier.rs:45-49 (`struct Evaluated<F, CS> {
    committed: Committed<F, CS>, evaluated: logup::Evaluated<F> }`). -/
structure Evaluated (F G₁ : Type) where
  committed : Committed G₁
  evaluated : Evals F

/-- `Vec[i]` in Rust, where an out-of-bounds index is a panic (rule R4). The same
    four lines as `Permutation.atIndex`; it cannot live in a shared lower module
    because Exec/Arith and Exec/Query are boundary files for this package. -/
def atIndex {alpha : Type} (xs : Array alpha) (i : Nat) (site : String) :
    Except Fault alpha :=
  match xs[i]? with
  | some x => .ok x
  | none => .error (Fault.panic site)

/-- rust: the `query.index.unwrap()` *and* the slice index in the closures at
    logup.rs:423-425. A query that reaches the verifier with `index := none` was
    never numbered by the constraint system, and the index into the evaluation
    vector is a second, separate abort on the same line. Both report the line the
    Rust would name. -/
def indexQuery {p : ℕ} [Fact (Nat.Prime p)] (xs : Array (Fr p)) (i : Option Nat)
    (site : String) : Except Fault (Fr p) := do
  let i ← match i with
    | none => .error (Fault.panic site)
    | some i => .ok i
  atIndex xs i site

/-- rust: proofs/src/plonk/logup.rs:416-434 (`evaluate_expressions`), the ten
    closures `Expression::evaluate` is called with.

    docs/REVIEW.md R-12: the virtual-selector panic is *here*, in the caller's
    closure, not inside `Expression.evaluate` - which is why Exec/Circuit
    deliberately has no `Fault`-returning evaluate. The port realises the panic
    by instantiating evaluate's result type at `Except Fault (Fr p)`, so the
    nine other closures become monadic versions of the same arithmetic and the
    first error short-circuits the rest of the traversal, exactly as a Rust
    `panic!` unwinds out of it. -/
def evalCallbacks {p : ℕ} [Fact (Nat.Prime p)]
    (adviceEvals fixedEvals instanceEvals challenges : Array (Fr p)) :
    Expression.Callbacks (Fr p) (Except Fault (Fr p)) :=
  { constant := fun s => .ok s
    selectorColumn := fun _ => .error (Fault.panic "proofs/src/plonk/logup.rs:422")
    fixedColumn := fun q => indexQuery fixedEvals q.index "proofs/src/plonk/logup.rs:423"
    adviceColumn := fun q => indexQuery adviceEvals q.index "proofs/src/plonk/logup.rs:424"
    instanceColumn := fun q => indexQuery instanceEvals q.index "proofs/src/plonk/logup.rs:425"
    challenge := fun c => atIndex challenges c.index "proofs/src/plonk/logup.rs:426"
    negated := fun a => do let a ← a; return -a
    sum := fun a b => do let a ← a; let b ← b; return a + b
    product := fun a b => do let a ← a; let b ← b; return a * b
    scaled := fun a s => do let a ← a; return a * s }

/-- rust: proofs/src/plonk/logup/verifier.rs:51-69
    (`ChunkedArgument::read_multiplicities`), called at plonk/verifier.rs:161.

    The Rust reads nothing off `self`: the multiplicities commitment is one point
    per *argument*, not per chunk, which is the whole point of the shared m. -/
def readMultiplicities {F : Type} {G₁ : Type} (_argument : LogupChunkedArgument F)
    (h : Hashable G₁) : TranscriptM (CommittedMultiplicities G₁) := do
  let multiplicities ← tmRead h
  return { multiplicities }

/-- rust: proofs/src/plonk/logup/verifier.rs:72-110
    (`CommittedMultiplicities::read_commitment`), called at plonk/verifier.rs:189
    with `batch.num_chunks()`.

    `nb_chunks` helper commitments, then one accumulator. The count comes from
    the *chunked argument*, which the caller rebuilds with `chunk_by_degree` a
    second time (verifier.rs:161 and :188 each call it), so the transcript layout
    depends on `cs_degree` being the same at both sites and on chunking being a
    pure function of the constraint system. -/
def CommittedMultiplicities.readCommitment {G₁ : Type}
    (cm : CommittedMultiplicities G₁) (nbChunks : Nat) (h : Hashable G₁) :
    TranscriptM (Committed G₁) := do
  let helperPolys ← tmReadN h nbChunks
  let accumulator ← tmRead h
  return { multiplicities := cm.multiplicities, helperPolys, accumulator }

/-- rust: proofs/src/plonk/logup/verifier.rs:113-168 (`Committed::evaluate`),
    called at plonk/verifier.rs:426.

    Order: m_eval, then one h_i_eval per chunk, then Z_eval, then
    `Z(omega*x)_eval` - so `nb_chunks + 3` scalars, and the helper count is taken
    from the *commitments* (`self.helper_polys.len()`, :127), not from the
    constraint system. If the two disagreed the transcript would desynchronise
    silently; they cannot disagree for anything `readCommitment` built. -/
def Committed.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (coms : Committed G₁) :
    TranscriptM (Evaluated (Fr p) G₁) := do
  let nbChunks := coms.helperPolys.size
  let multiplicitiesEval ← tmRead hashableFr
  let helperEvals ← tmReadN hashableFr nbChunks
  let accumulatorEval ← tmRead hashableFr
  let accumulatorNextEval ← tmRead hashableFr
  return { committed := coms,
           evaluated := { multiplicitiesEval, helperEvals, accumulatorEval,
                          accumulatorNextEval } }

/-- rust: proofs/src/plonk/logup/verifier.rs:171-211 (`Evaluated::queries`),
    reached at plonk/verifier.rs:625.

    m at x, each h_i at x, then Z at x and at omega*x. Unlike the permutation's
    `queries` this one cannot fail: the helper loop
    (`helper_polys.iter().zip(helper_evals.iter())`, :187-192) *zips* rather than
    indexing, so a length mismatch truncates instead of panicking, and every
    commitment is reached by field access rather than by index. The truncation is
    still observable: a proof that under-reads the helper evals simply contributes
    fewer openings, and the identity check is where it fails.

    The Rust takes `vk: &VerifyingKey<F, CS>` and reads only `vk.domain` (:178);
    the port takes the domain, as Exec/Permutation does. -/
def Evaluated.queries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (ev : Evaluated (Fr p) G₁) (domain : EvaluationDomain (Fr p)) (x : Fr p) :
    Array (VerifierQuery (Fr p) G₁) :=
  let xNext := domain.rotateOmega x Rotation.next
  -- verifier.rs:180-185
  let mQuery := [VerifierQuery.new x CommitmentLabel.noLabel
                    ev.committed.multiplicities ev.evaluated.multiplicitiesEval]
  -- verifier.rs:187-193
  let helperQueries := (List.zip ev.committed.helperPolys.toList
                                          ev.evaluated.helperEvals.toList).map
    fun (com, eval) => VerifierQuery.new x CommitmentLabel.noLabel com eval
  -- verifier.rs:195-208
  let zQueries := [ VerifierQuery.new x CommitmentLabel.noLabel ev.committed.accumulator
                      ev.evaluated.accumulatorEval,
                    VerifierQuery.new xNext CommitmentLabel.noLabel
                      ev.committed.accumulator ev.evaluated.accumulatorNextEval ]
  (mQuery ++ helperQueries ++ zQueries).toArray

/-- rust: proofs/src/plonk/logup.rs:442-443
    (`evaluate_expressions(slice::from_ref(&argument.selector)).swap_remove(0)`).
    The vector always has exactly one element, so the index cannot fail; it is
    kept as a panic site because `swap_remove` is a `Vec` operation and rule R4
    does not assume. -/
def swapRemove0 {alpha : Type} (xs : Array alpha) : Except Fault alpha :=
  match xs[0]? with
  | some x => .ok x
  | none => .error (Fault.panic "proofs/src/plonk/logup.rs:443")

/-- rust: proofs/src/plonk/logup.rs:383-482 (`Evaluated::expressions`), the two
    LogUp identities, reached from `partially_evaluate_identities` at
    plonk/mod.rs:574.

    THREE constraints, in this order: the boundary `(l_0 + l_last) * Z(x)` (:445),
    one helper constraint per chunk (:448-467), then the accumulator constraint
    (:471-477). The chunk loop's `sum_helpers` accumulates *while* the helper
    constraints are produced (:464) and the accumulator constraint uses the total,
    so the shared-helper sum is over the zipped pairs only.

    Two things the port has to keep honest:
      * `argument.input_expression_chunks().zip(self.helper_evals.iter())`
        (:448-451) truncates to the shorter input (rule R3). A proof that read
        fewer helper evals than the argument has chunks silently drops the missing
        chunks' constraints *and* their contribution to `sum_helpers`.
      * `product * f.invert().unwrap()` (:460) is a hard abort when any
        `f_j(x) + beta = 0`. This is docs/REVIEW.md R-2's second face: the
        argument divides by a value whose numerator the prover controls, and the
        partial-product trick recomputes each partial product by *inverting*
        rather than by a zero-safe prefix/suffix recurrence, so one zero factor
        kills the verifier instead of the proof. Over the honest prover the factor
        is non-zero because beta is squeezed after the inputs are committed; a
        malicious prover can still aim for it. -/
def expressions {p : ℕ} [Fact (Nat.Prime p)]
    (ev : Evals (Fr p)) (l0 lLast lBlind theta beta : Fr p)
    (argument : LogupChunkedArgument (Fr p))
    (adviceEvals fixedEvals instanceEvals challenges : Array (Fr p)) :
    Except Fault (Array (Fr p)) := do
  -- logup.rs:415
  let activeRows := 1 - (lLast + lBlind)
  let cb := evalCallbacks adviceEvals fixedEvals instanceEvals challenges
  -- logup.rs:416-434
  let evaluateExpressions (exprs : Array (Expression (Fr p))) :
      Except Fault (Array (Fr p)) :=
    mapExceptArray (fun e => Expression.evaluate cb e) exprs
  -- logup.rs:435-439: fold(F::ZERO, |acc, eval| acc * theta + eval)
  let compressExpressions (exprs : Array (Expression (Fr p))) :
      Except Fault (Fr p) := do
    let vs ← evaluateExpressions exprs
    return vs.foldl (init := 0) fun acc v => acc * theta + v
  -- logup.rs:441
  let compressedTable ← compressExpressions argument.tableExpressions
  -- logup.rs:442-443
  let sel ← swapRemove0 (← evaluateExpressions #[argument.selector])
  -- logup.rs:445
  let boundary := (l0 + lLast) * ev.accumulatorEval
  -- logup.rs:447-467
  let pairs := List.zip argument.inputExpressionChunks.toList ev.helperEvals.toList
  let mut sumHelpers : Fr p := 0
  let mut helperConstraints : Array (Fr p) := #[]
  for (chunk, helperEval) in pairs do
    let withBeta ← mapExceptArray
      (fun input => do pure ((← compressExpressions input) + beta)) chunk
    let product := withBeta.foldl (init := 1) (fun a b => a * b)
    let partials ← mapExceptArray (fun f => match invert f with
        | none => .error (Fault.panic "proofs/src/plonk/logup.rs:460")
        | some fi => .ok (product * fi)) withBeta
    let sum := partials.foldl (init := 0) (fun a b => a + b)
    sumHelpers := sumHelpers + helperEval
    helperConstraints := helperConstraints.push (helperEval * product - sum)
  -- logup.rs:471-477
  let diff := ((ev.accumulatorNextEval - ev.accumulatorEval - sel * sumHelpers)
                * (compressedTable + beta)) + ev.multiplicitiesEval
  let accumulatorConstraint := diff * activeRows
  return #[boundary] ++ helperConstraints ++ #[accumulatorConstraint]

/-! rust: the `#[cfg(feature = "solidity-verifier-trace")]` blocks in
    logup/verifier.rs - NOT ported, in any of the three modules that read this Rust.
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

/-! rust: proofs/src/plonk/logup.rs:178-187 and :205-214 (the two `Debug` impls)
    - NOT ported. They are `derive`-shaped formatting with a hand-written field
    list, reached only through `{:?}`; the only verifier-reachable `{:?}` in the
    plonk layer is `PinnedConstraintSystem` (plonk/mod.rs:272), which does not
    format a lookup argument. Exec/Circuit.lean records the same call for
    `Debug for Advice`. -/

/-! rust: proofs/src/plonk/logup.rs:277-311 (`BatchedArgument::new`) - NOT
    verifier-reachable: its only callers are plonk/circuit.rs:1940 and :2000,
    inside `batched_lookup` and `batch_lookup_any`, i.e. circuit construction,
    which plan Section 1 puts out of scope. Already recorded in Exec/Circuit.lean
    with its two panic sites (`input_expressions[0].len()` at :291 and the
    ragged-map `assert_eq!` at :296). The accessors `selector_expression`
    (:340-342, :363-366) and `table_expressions` (:345-347, :369-371) are the
    projections of the same-named fields in the port and are reached only from
    plonk/evaluation.rs:276 and :320, which is the prover's constraint compiler.
    `input_expression_chunks` (:359-361) is the projection of the field that
    `expressions` above consumes at logup.rs:449, and is also reached from the
    generator at solidity-verifier/src/lowering/quotient.rs:1432. -/

/-! ## Known-answer checks

Hand-computed over `Fr 17`. The commitment type is `Nat` with `hashableU32` so
the reads are 4 bytes wide and no curve is needed; the scalar reads use the real
`hashableFr`. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def bytesOf (vals : List Nat) (w : Nat) : Bytes :=
  vals.foldl (fun acc v => ByteArray.append acc (natToBytesLE v w)) Bytes.empty

/-- The width-1, one-chunk lookup argument the checks use: selector 1, one
    parallel lookup whose single input is advice column 0, table 7. -/
def katChunked : LogupChunkedArgument (Fr 17) :=
  { name := "l"
    selector := Expression.constant 1
    inputExpressionChunks := #[#[#[Expression.advice
        { index := some 0, columnIndex := 0, rotation := Rotation.cur,
          phase := { val := 0 } }]]]
    tableExpressions := #[Expression.constant 7] }

def katEvals : Evals (Fr 17) :=
  { multiplicitiesEval := 2, helperEvals := #[4], accumulatorEval := 5,
    accumulatorNextEval := 6 }

/-- `read_multiplicities` then `read_commitment 2`: one point, then two helpers
    and one accumulator - four points, 16 bytes, and the accumulator is the last
    one read. Then `evaluate`: `nb_chunks + 3` = 5 scalars. -/
def readKats_ok : Bool :=
  let buf := bytesOf [11, 21, 22, 23] 4
  match (readMultiplicities katChunked hashableU32).run (Transcript.initFromBytes buf) with
  | .error _ => false
  | .ok (cm, t1) =>
      cm.multiplicities == 11 && t1.pos == 4 &&
      (match (cm.readCommitment 2 hashableU32).run t1 with
       | .error _ => false
       | .ok (c, t2) =>
           c.multiplicities == 11 && c.helperPolys.toList == [21, 22] &&
           c.accumulator == 23 && t2.pos == 16)
      && match (({ multiplicities := 1, helperPolys := #[7, 8], accumulator := 9 }
                  : Committed Nat)).evaluate (p := 17) |>.run
              (Transcript.initFromBytes (bytesOf [1, 2, 3, 4, 5] 32)) with
         | .error _ => false
         | .ok (ev, t3) =>
             t3.pos == 5 * 32 &&
             ev.evaluated.multiplicitiesEval.val == 1 &&
             (ev.evaluated.helperEvals.map fun v => v.val) == #[2, 3] &&
             ev.evaluated.accumulatorEval.val == 4 &&
             ev.evaluated.accumulatorNextEval.val == 5

/-- `queries`: m at x, the two helpers at x, then Z at x and at omega*x. Over
    the `ZMod 17` domain (omega = 13) with x = 5, x_next = 5*13 = 14. Five
    queries, and only the last one is at x_next. -/
def queriesKats_ok : Bool :=
  let ev : Evaluated (Fr 17) Nat :=
    { committed := { multiplicities := 1, helperPolys := #[7, 8], accumulator := 9 },
      evaluated := { katEvals with helperEvals := #[4, 3] } }
  match EvaluationDomain.new (F := Fr 17) fc17 1 2 with
  | .error _ => false
  | .ok d =>
      let qs := ev.queries (p := 17) d 5
      qs.size == 5 &&
      (qs.map fun q => q.point.val) == #[5, 5, 5, 5, 14] &&
      (qs.map fun q => q.eval.val) == #[2, 4, 3, 5, 6] &&
      (qs.map fun q => match q.commitment with
        | .onePiece c => c
        | .linear _ _ _ => 0) == #[1, 7, 8, 9, 9] &&
      -- the helper zip truncates: one helper eval against two commitments gives
      -- four queries, not five, and nothing fails
      (let ev' : Evaluated (Fr 17) Nat :=
          { ev with evaluated := { katEvals with helperEvals := #[4] } }
       (ev'.queries (p := 17) d 5).size == 4)

/-- The two identities, one chunk, hand-computed over `Fr 17` with theta = 2,
    beta = 3, l_0 = 5, l_last = 2, l_blind = 3, advice column 0 evaluating to 9:
      compressed_table = 7, selector = 1, compressed input + beta = 9 + 3 = 12
      boundary  = (l_0 + l_last) * Z = (5 + 2) * 5 = 35 = 1
      product   = 12;  partial = 12 * 12^-1 = 1;  sum = 1
      helper    = h * product - sum = 4*12 - 1 = 47 = 13
      sum_helpers = 4
      diff = (Z_next - Z - s * sum_h) * (t + beta) + m
           = (6 - 5 - 4) * 10 + 2 = -3*10 + 2 = -28 = 6
      active_rows = 1 - (2 + 3) = -4 = 13
      accumulator = 6 * 13 = 78 = 10
    so the answer is `#[1, 13, 10]`. -/
def expressionsKats_ok : Bool :=
  match expressions (p := 17) katEvals 5 2 3 2 3 katChunked #[9] #[] #[] #[] with
  | .error _ => false
  | .ok out => out.map (fun v => v.val) == #[1, 13, 10]

/-- R-2's second face: `f_j(x) + beta = 0` makes the partial-product inversion
    at logup.rs:460 abort. Here the advice eval is 14 and beta = 3, so the factor
    is 0 in `Fr 17`. -/
def expressionsPanic_kats_ok : Bool :=
  match expressions (p := 17) katEvals 5 2 3 2 3 katChunked #[14] #[] #[] #[] with
  | .error (Fault.panic "proofs/src/plonk/logup.rs:460") => true
  | _ => false

/-- R-12: a virtual selector in a lookup expression panics in the *caller's*
    closure, at logup.rs:422, not inside `Expression.evaluate`. -/
def virtualSelector_kats_ok : Bool :=
  let bad := { katChunked with selector := (Expression.selector
      { index := 0, isSimple := false }) }
  match expressions (p := 17) katEvals 5 2 3 2 3 bad #[9] #[] #[] #[] with
  | .error (Fault.panic "proofs/src/plonk/logup.rs:422") => true
  | _ => false

/-- Two chunks but one helper eval: the zip truncates, so only one helper
    constraint is emitted *and* `sum_helpers` sees only that one. With both
    chunks present, chunk 1 is the constant 1, so its factor is 1 + 3 = 4, its
    partial product is 4 * 4^-1 = 1 and its constraint is 1*4 - 1 = 3, while
    sum_helpers becomes 4 + 1 = 5, so the accumulator constraint is
    `(6 - 5 - 5)*10 + 2 = -38 = 13` scaled by 13 again, i.e. 16. -/
def zipTruncation_kats_ok : Bool :=
  let two := { katChunked with
    inputExpressionChunks := #[#[#[Expression.constant 9]],
                               #[#[Expression.constant 1]]] }
  match expressions (p := 17) katEvals 5 2 3 2 3 two #[] #[] #[] #[] with
  | .error _ => false
  | .ok out =>
      out.map (fun v => v.val) == #[1, 13, 10] &&
      (match expressions (p := 17)
          { katEvals with helperEvals := #[4, 1] } 5 2 3 2 3 two #[] #[] #[] #[] with
       | .error _ => false
       | .ok out2 => out2.map (fun v => v.val) == #[1, 13, 3, 16])

end Kats

#eval readKats_ok                      -- expect true
#eval queriesKats_ok                   -- expect true
#eval expressionsKats_ok               -- expect true
#eval expressionsPanic_kats_ok         -- expect true
#eval virtualSelector_kats_ok          -- expect true
#eval zipTruncation_kats_ok            -- expect true

end Logup

end Midfall.Halo2

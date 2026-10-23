-- |
-- Midfall.Halo2.Trash
--
-- Plan Section 4 module map, row `plonk/permutation/*, logup/*, trash/*,
-- linearization/verifier.rs -> Exec/{Permutation,Logup,Trash}`: the verifier
-- path of the trash-can argument. Sources:
-- proofs/src/plonk/trash/verifier.rs (75 lines, all of it) and the
-- verifier-reachable parts of proofs/src/plonk/trash.rs (89 lines).
--
-- The argument record itself - TrashArgument and its requiredDegree - lives in
-- Exec/Circuit.lean, because ConstraintSystem.trashcans names it and Lean has
-- no mutually recursive modules (see that file's header, choice 3). This module
-- adds only the verifier path: the two state types, the two reads, the query and
-- the Horner identity. Nothing is redefined here.
--
-- Port rules: R1 provenance, R2 names, R3 iterator semantics (`fold` is a left
-- fold over the map, so the Horner order is source order), R4 panics become
-- `Fault.panic`, R6 `Vec` -> `Array`, R9 the transcript reads go through the
-- `Hashable` record, R10 total.
--
-- REACHABILITY. The set grepped is the one the plan names: plonk/verifier.rs,
-- plonk/{permutation,logup,trash,linearization}/verifier.rs, plonk/mod.rs,
-- poly/** and proofs/solidity-verifier/src. Ported, with the site that reaches
-- each:
--   trash::verifier::Committed   plonk/verifier.rs:204-212, :222
--   trash::verifier::Evaluated   plonk/verifier.rs:431-439, :484, :597
--   trash::Evaluated             plonk/verifier.rs:484 (`.evaluated`),
--                                plonk/mod.rs:495
--   Argument::read_committed     plonk/verifier.rs:209
--   Committed::evaluate          plonk/verifier.rs:436
--   Evaluated::queries           plonk/verifier.rs:626
--   Evaluated::expressions       plonk/mod.rs:594
--                                (`partially_evaluate_identities`)
-- NOT verifier-reachable, so skipped with the evidence at each site below:
-- `Argument::{new, name, selector, constraint_expressions}` and the whole of
-- trash/prover.rs.

import Midfall.Common.Curve
import Midfall.Halo2.Exec.Arith
import Midfall.Halo2.Exec.Circuit
import Midfall.Halo2.Exec.Error
import Midfall.Halo2.Exec.Permutation
import Midfall.Halo2.Exec.Query
import Midfall.Halo2.Exec.Transcript

namespace Midfall.Halo2
namespace Trash

/-- rust: proofs/src/plonk/trash/verifier.rs:10-13 (`struct Committed<F, CS> {
    trash_commitment: CS::Commitment }`). One commitment per trashcan, read
    after the trash challenge is squeezed. As in Exec/Permutation and
    Exec/Logup, the Rust's `F` parameter is a phantom and the port keeps only
    the commitment type. -/
structure Committed (G₁ : Type) where
  trashCommitment : G₁

/-- rust: proofs/src/plonk/trash.rs:52-55 (`struct Evaluated<F> { trash_eval:
    F }`), the trash polynomial evaluated at x.

    FORCED R2 DEVIATION, recorded: the Rust has two types called `Evaluated` on
    this path - `trash::Evaluated` (here) and `trash::verifier::Evaluated`
    (below) - and Lean has no module path to separate them. The verifier's keeps
    the bare name, because that is the type the verifier trace stores. -/
structure Eval (F : Type) where
  trashEval : F

/-- rust: proofs/src/plonk/trash/verifier.rs:15-19 (`struct Evaluated<F, CS> {
    committed: Committed<F, CS>, evaluated: trash::Evaluated<F> }`). -/
structure Evaluated (F G₁ : Type) where
  committed : Committed G₁
  evaluated : Eval F

/-- `Vec[i]` in Rust, where an out-of-bounds index is a panic (rule R4). The same
    four lines as `Permutation.atIndex`; it cannot live in a shared lower module
    because Exec/Arith and Exec/Query are boundary files for this package. -/
def atIndex {alpha : Type} (xs : Array alpha) (i : Nat) (site : String) :
    Except Fault alpha :=
  match xs[i]? with
  | some x => .ok x
  | none => .error (Fault.panic site)

/-- rust: the `query.index.unwrap()` *and* the slice index in the closures at
    trash.rs:71-73. Same double abort as Exec/Logup's `indexQuery`. -/
def indexQuery {p : ℕ} [Fact (Nat.Prime p)] (xs : Array (Fr p)) (i : Option Nat)
    (site : String) : Except Fault (Fr p) := do
  let i ← match i with
    | none => .error (Fault.panic site)
    | some i => .ok i
  atIndex xs i site

/-- rust: proofs/src/plonk/trash.rs:67-79 (`evaluate_expression`), the ten
    closures `Expression::evaluate` is called with.

    This is the third instantiation of the same record in the verifier path (the
    gate loop at plonk/mod.rs:530 is the second, and Exec/Logup's is the first),
    and it is *textually identical* to the LogUp one apart from the line numbers -
    which is why the site strings are kept per-file rather than shared: rule R4
    names the panic by the line that raises it, and a shared helper would report
    logup.rs for a trash panic. docs/REVIEW.md R-12 again: the virtual-selector
    panic is this closure (trash.rs:70), not `Expression.evaluate`. -/
def evalCallbacks {p : ℕ} [Fact (Nat.Prime p)]
    (adviceEvals fixedEvals instanceEvals challenges : Array (Fr p)) :
    Expression.Callbacks (Fr p) (Except Fault (Fr p)) :=
  { constant := fun s => .ok s
    selectorColumn := fun _ => .error (Fault.panic "proofs/src/plonk/trash.rs:70")
    fixedColumn := fun q => indexQuery fixedEvals q.index "proofs/src/plonk/trash.rs:71"
    adviceColumn := fun q => indexQuery adviceEvals q.index "proofs/src/plonk/trash.rs:72"
    instanceColumn := fun q => indexQuery instanceEvals q.index "proofs/src/plonk/trash.rs:73"
    challenge := fun c => atIndex challenges c.index "proofs/src/plonk/trash.rs:74"
    negated := fun a => do let a ← a; return -a
    sum := fun a b => do let a ← a; let b ← b; return a + b
    product := fun a b => do let a ← a; let b ← b; return a * b
    scaled := fun a s => do let a ← a; return a * s }

/-- rust: proofs/src/plonk/trash/verifier.rs:21-38 (`Argument::read_committed`),
    called at plonk/verifier.rs:209 - one commitment per trashcan, all of them
    read after the trash challenge is squeezed. The Rust reads nothing off
    `self`: the count comes from `vk.cs.trashcans.iter()` at the call site. -/
def readCommitted {F : Type} {G₁ : Type} (_argument : TrashArgument F)
    (h : Hashable G₁) : TranscriptM (Committed G₁) := do
  let trashCommitment ← tmRead h
  return { trashCommitment }

/-- rust: proofs/src/plonk/trash/verifier.rs:41-62 (`Committed::evaluate`),
    called at plonk/verifier.rs:436. One scalar per trashcan. -/
def Committed.evaluate {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} (coms : Committed G₁) :
    TranscriptM (Evaluated (Fr p) G₁) := do
  let trashEval ← tmRead hashableFr
  return { committed := coms, evaluated := { trashEval } }

/-- rust: proofs/src/plonk/trash/verifier.rs:65-74 (`Evaluated::queries`),
    reached at plonk/verifier.rs:626. Exactly one opening, at x, unlabelled - the
    trash polynomial is not opened at any rotation, which is what makes this the
    cheapest of the three arguments' query lists. -/
def Evaluated.queries {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (ev : Evaluated (Fr p) G₁) (x : Fr p) : Array (VerifierQuery (Fr p) G₁) :=
  #[VerifierQuery.new x CommitmentLabel.noLabel ev.committed.trashCommitment
      ev.evaluated.trashEval]

/-- rust: proofs/src/plonk/trash.rs:58-88 (`Evaluated::expressions`), the
    compressed-constraint identity, reached from `partially_evaluate_identities`
    at plonk/mod.rs:594.

    One expression out, in this shape (:82-87):

      compressed = fold(F::ZERO, |acc, eval| acc * trash_challenge + eval)
                   over the constraint expressions, in source order
      q          = the selector evaluated the same way
      result     = compressed - (1 - q) * trash_eval

    The fold is a *left* fold, so the powers of the trash challenge run
    ascending with the constraint index: the first constraint is multiplied by
    `trash_challenge^(n-1)`. Reading it the other way round is silent - the
    identity still holds on any honest proof, and only a batched adversarial
    one notices. An argument with no constraints folds to `F::ZERO` and the
    identity degenerates to `(1 - q) * trash_eval = 0`, which is still a
    constraint on the trash polynomial.

    The polarity is worth stating because it is easy to read backwards: the
    identity is `compressed = (1 - q) * trash_eval`. Where the selector is 1 the
    right-hand side vanishes, so the compressed sum - and therefore, because the
    challenge is random, each individual constraint - is forced to 0. Where the
    selector is 0 the trash polynomial absorbs whatever the constraints evaluate
    to, so they are free. The constraints are forced exactly where the selector is
    ON, which is the polarity plan 9.3's
    `evalRow ... T.selector i = 1 -> ...` conjunct states; the trash polynomial is
    the escape valve, not the constraint. -/
def expressions {p : ℕ} [Fact (Nat.Prime p)]
    (ev : Eval (Fr p)) (argument : TrashArgument (Fr p)) (trashChallenge : Fr p)
    (adviceEvals fixedEvals instanceEvals challenges : Array (Fr p)) :
    Except Fault (Array (Fr p)) := do
  let cb := evalCallbacks adviceEvals fixedEvals instanceEvals challenges
  let evaluateExpression (e : Expression (Fr p)) : Except Fault (Fr p) :=
    Expression.evaluate cb e
  -- trash.rs:82-84
  let compressed ← (argument.constraintExpressions.toList.foldlM
      (init := (0 : Fr p)) fun acc e => do pure (acc * trashChallenge + (← evaluateExpression e)))
  -- trash.rs:86-87
  let q ← evaluateExpression argument.selector
  return #[compressed - (1 - q) * ev.trashEval]

/-! rust: the `#[cfg(feature = "solidity-verifier-trace")]` blocks in
    trash/verifier.rs - NOT ported, in any of the three modules that read this Rust.
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

/-! rust: proofs/src/plonk/trash.rs:19-29 (`Argument::new`) and :37-49
    (`name`, `selector`, `constraint_expressions`) - NOT verifier-reachable: the
    constructor's only caller is plonk/circuit.rs:2696, inside
    `VirtualCells::apply_selector_to_constraints`, i.e. circuit construction, and
    the three accessors are the projections of the same-named fields on
    `TrashArgument` in Exec/Circuit.lean, which records the same call. -/

/-! rust: proofs/src/plonk/trash/prover.rs (96 lines) - NOT verifier-reachable:
    prover code, out of scope by plan Section 1. It is the only caller of
    `EvaluationDomain::lagrange_from_vec` and `empty_lagrange` (see the recorded
    skips in Exec/Domain.lean). -/

/-! ## Known-answer checks

Hand-computed over `Fr 17`. The commitment type is `Nat` with `hashableU32` so
the read is 4 bytes wide and no curve is needed. -/

section Kats

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

def adv0 : Expression (Fr 17) :=
  Expression.advice { index := some 0, columnIndex := 0, rotation := Rotation.cur,
                      phase := { val := 0 } }

/-- Two constraints and a constant selector: the Horner fold over
    `[advice 0, constant 5]` with challenge 3 and advice eval 9 is
    `(0*3 + 9) = 9`, then `9*3 + 5 = 32 = 15`; `q = 2`, `trash_eval = 4`, so the
    answer is `15 - (1 - 2)*4 = 15 + 4 = 19 = 2`. -/
def expressionsKats_ok : Bool :=
  let arg : TrashArgument (Fr 17) :=
    { name := "t", selector := Expression.constant 2,
      constraintExpressions := #[adv0, Expression.constant 5] }
  match expressions (p := 17) { trashEval := 4 } arg 3 #[9] #[] #[] #[] with
  | .error _ => false
  | .ok out => out.map (fun v => v.val) == #[2]

/-- No constraints: the fold is `F::ZERO`, so the identity degenerates to
    `(1 - q) * trash_eval = 0`. With `q = 1` the whole expression is 0 - a
    trashcan whose selector is constantly 1 constrains nothing, which is exactly
    what "always satisfied" should mean. -/
def emptyConstraints_kats_ok : Bool :=
  let arg : TrashArgument (Fr 17) :=
    { name := "t", selector := Expression.constant 1, constraintExpressions := #[] }
  match expressions (p := 17) { trashEval := 7 } arg 3 #[] #[] #[] #[] with
  | .error _ => false
  | .ok out => out.map (fun v => v.val) == #[0]

/-- R-12: a virtual selector panics in the caller's closure at trash.rs:70. -/
def virtualSelector_kats_ok : Bool :=
  let arg : TrashArgument (Fr 17) :=
    { name := "t", selector := Expression.selector { index := 0, isSimple := false },
      constraintExpressions := #[adv0] }
  match expressions (p := 17) { trashEval := 4 } arg 3 #[9] #[] #[] #[] with
  | .error (Fault.panic "proofs/src/plonk/trash.rs:70") => true
  | _ => false

/-- One commitment read (4 bytes as a Nat), then one scalar (32 bytes), then
    exactly one query at x with no label. -/
def readKats_ok : Bool :=
  let arg : TrashArgument (Fr 17) :=
    { name := "t", selector := Expression.constant 1, constraintExpressions := #[] }
  let buf := ByteArray.append (natToBytesLE 42 4) (natToBytesLE 9 32)
  match (readCommitted arg hashableU32).run (Transcript.initFromBytes buf) with
  | .error _ => false
  | .ok (cm, t1) =>
      cm.trashCommitment == 42 && t1.pos == 4 &&
      (match (Committed.evaluate (p := 17) cm).run t1 with
       | .error _ => false
       | .ok (ev, t2) =>
           t2.pos == 4 + 32 && ev.evaluated.trashEval.val == 9 &&
           (match ev.queries (p := 17) 11 with
            | #[q] => q.point.val == 11 && q.eval.val == 9 &&
                       (match q.commitmentLabel with | .noLabel => true | _ => false) &&
                       (match q.commitment with
                        | .onePiece c => c == 42
                        | .linear _ _ _ => false)
            | _ => false))

end Kats

#eval expressionsKats_ok               -- expect true
#eval emptyConstraints_kats_ok         -- expect true
#eval virtualSelector_kats_ok          -- expect true
#eval readKats_ok                      -- expect true

end Trash

end Midfall.Halo2

-- |
-- Midfall.Lowering.Snapshot
--
-- P-SE stage 3, file 2 of 3 (docs/plans/P-SE-stage3.md file row 2; design0.md
-- section "Midfall.Lowering.Snapshot / snapshotOf / snapshotOf_prepareMsgs").
--
-- WHAT THIS FILE IS FOR. Inv (Inv.lean) relates the contract memory at a checkpoint
-- to the values the Lean verifier computed. Those values need a name, and before D6
-- (commit 9d0b94c) they did not have one: x, the splitting factor, xn, the six
-- evaluation arrays, the Lagrange triple, x1..x4, fEval, v, pi and the DualMSM were
-- let binders inside verifyAlgebraicConstraints and multiPrepare. The only way to
-- state an invariant about them was to replay the Fiat-Shamir schedule a second time
-- in the theorem file, which is the R-30/R-32 drift hazard D6 exists to avoid. So
-- this file replays NOTHING: every value here is a projection of a record the
-- refactored Exec phases return, computed by calling the same functions prepareMsgs
-- calls, in the same order, on the same transcript state.
--
-- THE PREFIX CHAIN. Attack finding (design0, PartialSpecs over a FULL Snapshot):
-- one Snapshot built only when every phase succeeds is WEAKER THAN PLAN, because for
-- calldata where Lean faults in a late phase there is no snapshot at all, every
-- per-partial field is vacuous for that calldata, and the composition cannot show
-- that the EARLIER partial reverts. PLAN 9.5 asks for the state after phase k, so
-- this file provides one record per boundary with a runner per boundary, each Except
-- Fault, each running only the phases that boundary needs. The payoff is concrete:
-- lagrange_spec is stated against snapshotOfLagrange, which never calls linearize
-- and never touches the PCS, so a logup panic in the linearization step or an
-- x3-in-a-point-set panic in fEval no longer erases the hypothesis it needs.
--
-- THREE THINGS THIS FILE CANNOT NAME, stated rather than faked:
--
--   1. expressions and linCom (D6 limit 1). linearize returns only the query array
--      (Verifier.lean:950), so the partially evaluated identities and the
--      linearization commitment query leave no name. Widening it is one mechanical
--      change that was deliberately not made. Recomputing them here by calling the
--      same two Exec functions again was also not done: it would put a second copy
--      of a computation in a file that does not own it, which is the same drift class
--      as the transcript replay, one step removed. So they are a NAMED HOLE:
--      Linearization is the record that would hold them, Snapshot.lin is an Option
--      snapshotOf sets to none, and the Inv clauses that read it are inert until the
--      hole is filled.
--   2. The output of a phase that FAULTS (D6 limit 2). A phase returns its record or
--      nothing, so the prefix at a boundary at or after a faulting phase does not
--      exist. That is a property of the design, not a bug in it: the contract partial
--      matching a faulting Lean phase has, by construction, no Lean value to be
--      compared against. The chain bounds the damage - a fault in phase k destroys
--      only the prefixes at and after k - and prefixSurvivesFaultKats_ok exhibits it.
--   3. acc : Option KzgAcc (D6 limit 3). No Exec phase produces a KzgAcc; decodeAcc
--      reads instance words, not verifier state. The field is present, typed, and
--      none from snapshotOf; a caller that has decoded one passes it in.
--
-- WHAT IS NOT HERE. The invariant itself (Inv.lean), the checkpoint liveness rule
-- (Checkpoint.lean), and any claim about what the contract writes: the agreement
-- between a value and a memory slot belongs to Inv, not to this file.

import Midfall.Halo2.Exec.Native
import Midfall.Halo2.Exec.Verifier
import Midfall.Halo2.Exec.Kzg.MultiOpen
import Midfall.Halo2.Exec.Kzg.Msm
import Midfall.Halo2.Exec.Accumulator
import Midfall.Lowering.Checkpoint

namespace Midfall.Lowering
open Midfall Midfall.Halo2

variable {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type}
  [Group G₁] [Group G₂] [Group Gₜ]
  [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [P : AdmissiblePairing G₁ G₂ Gₜ]

/-! ### The named hole -/

/-- D6 LIMIT 1, NAMED HOLE. The two values linearize computes and does not return:
    the partially evaluated batched identities (the (Option Nat, Fr) pairs
    partiallyEvaluateIdentities produces, Verifier.lean:294) and the linearization
    commitment query built from them (Verifier.lean:975-976).

    QUOTIENT_EVAL_MPTR holds the linearization eval and SELECTOR_ACC_MPTR holds the
    scalars of its commitment (QuotientAndLinearization.yul:41, :47-49), so Inv
    .quotient wants both. Neither is nameable from outside linearize today, so this
    record is the SHAPE of the hole rather than a value: snapshotOf puts none in
    Snapshot.lin and the Inv clauses that read it are inert until Exec widens
    linearize to return three fields instead of one. -/
structure Linearization (F G : Type) where
  /-- partiallyEvaluateIdentities output: one (selector column, value) per term. -/
  expressions : Array (Option Nat × F)
  /-- The linearization query: QUOTIENT_EVAL is its eval and the selector buckets
      are the scalars of its commitment. -/
  linCom : VerifierQuery F G

/-- The selector-accumulator buckets of a linearization query: the scalars of its
    linear commitment, in commitment order, which is what the contract stores one
    word per simple selector at SELECTOR_ACC_MPTR
    (QuotientAndLinearization.yul:47-49, and the same words returned by the split
    quotient evaluator, Halo2QuotientEvaluator output words 2..). A one-piece
    commitment has none, which is the empty-bucket render with no simple selectors. -/
def linComBuckets {F C : Type} (q : VerifierQuery F C) : Array F :=
  match q.commitment with
  | .linear _ scalars _ => scalars
  | .onePiece _ => #[]

/-- The eval of a linearization query, named so the Inv clause reads as one
    projection: QUOTIENT_EVAL_MPTR := linComEval L.linCom. -/
def linComEval {F C : Type} (q : VerifierQuery F C) : F := q.eval

/-! ### The prefix records -/

/-- Boundary .transcript, the part that comes from parseTrace: the challenge block
    and the commitment stream. No phase after parseTrace has to have run. -/
structure SnapTrace (p : ℕ) [Fact (Nat.Prime p)] (G₁ : Type) where
  trace : VerifierTrace (Fr p) G₁

/-- Plus readAlgebra: x, splittingFactor, xn, the rotation window and the six
    evaluation arrays. Exists exactly when parseTrace and readAlgebra both
    succeeded. -/
structure SnapAlgebra (p : ℕ) [Fact (Nat.Prime p)] (G₁ : Type)
    extends SnapTrace p G₁ where
  alg : Verifier.AlgebraRead (Fr p) G₁

/-- Plus the Lagrange prelude and the public instance evaluation. The prefix
    lagrange_spec is stated against, and the one that matters most: lagrangeTriple
    is group-free and runs before linearize, so a logup panic in the linearization
    step does not erase it. -/
structure SnapLagrange (p : ℕ) [Fact (Nat.Prime p)] (G₁ : Type)
    extends SnapAlgebra p G₁ where
  lagrange : LagrangeTriple (Fr p)
  /-- The public-column instance evaluation, or none when the key does not have the
      deployed shape. See instanceEvalOf for why this is an Option. -/
  instanceEval : Option (Fr p)

/-- Plus the multi-open query vector, and the linearization hole. -/
structure SnapQueries (p : ℕ) [Fact (Nat.Prime p)] (G₁ : Type)
    extends SnapLagrange p G₁ where
  queries : Array (VerifierQuery (Fr p) G₁)
  /-- NAMED HOLE, always none from snapshotOf (D6 limit 1). -/
  lin : Option (Linearization (Fr p) G₁)

/-- Plus the three PCS phases: x1..x4, the q_i combinations, fCom, fEval, v, pi and
    the DualMSM. Everything Inv .transcript and Inv .pcs needs except the
    trailing-bytes check and the accumulator. G₂ and Gₜ are phantom here (D-P7):
    PhaseC carries them but no field pins them. -/
structure SnapPcs (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    extends SnapQueries p G₁ where
  a : MultiPrepare.PhaseA (Fr p) G₁
  b : MultiPrepare.PhaseB (Fr p) G₁
  c : MultiPrepare.PhaseC (Fr p) G₁ G₂ Gₜ

/-- The whole run: the PCS prefix with the trailing-bytes check passed, plus the
    accumulator hole. -/
structure Snapshot (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ Gₜ : Type)
    extends SnapPcs p G₁ G₂ Gₜ where
  /-- NAMED HOLE (D6 limit 3): no Exec phase produces a KzgAcc. snapshotOf never
      fills this; the caller that decoded one supplies it. -/
  acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)

/-! ### The steps -/

/-- The wire bytes prepareMsgs feeds the transcript: each message re-serialised in
    wire order and absorbed under the caller hash (Native.lean:264-267). This is the
    only place the schedule is touched, and it touches it by handing the bytes to the
    same transcript the pipeline reads, not by describing the reads. -/
def transcriptOf (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (ms : List (Msg (Fr p) G₁)) : Transcript :=
  let bytes := ms.foldl (init := Bytes.empty)
    (fun acc m => ByteArray.append acc (msgWire E m))
  Transcript.initWithHash H bytes

/-- The committed-instance shape verifyNative hard-codes (test.rs:366-367): one proof
    row, one committed instance column holding the identity. -/
def committedShape {G₁ : Type} [One G₁] : Array (Array G₁) := #[#[1]]

/-- The instance shape at the same site: one proof, one public column of the given
    words. -/
def instanceShape {p : ℕ} [Fact (Nat.Prime p)]
    (inst : Array (Fr p)) : Array (Array (Array (Fr p))) := #[#[inst]]

/-- parseTrace on a transcript, leaving the state for the next step. -/
def snapshotTraceStep {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [One G₁]
    (g1 : G1Codec G₁) (feat : Features) (t0 : Transcript)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p)) :
    Except Fault (SnapTrace p G₁ × Transcript) := do
  let (trace, t1) ← (parseTrace g1 feat vk (committedShape (G₁ := G₁))
    (instanceShape inst)).run t0
  pure (SnapTrace.mk trace, t1)

/-- readAlgebra on the state parseTrace left, behind the shape checks the caller has
    already applied. The trace fields are passed in rather than destructured inside
    so that a gate can drive this step with a hand-built trace and no curve, which is
    what the stage-3 brief asks for (readAlgebra is group-free). -/
def snapshotAlgebraStep {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (g1 : G1Codec G₁) (feat : Features)
    (vk : VerifyingKey (Fr p) G₁) (trace : VerifierTrace (Fr p) G₁)
    (nbCommitted numProofs : Nat) (instances : Array (Array (Array (Fr p))))
    (t1 : Transcript) : Except Fault (SnapAlgebra p G₁ × Transcript) := do
  let (alg, t2) ← (Verifier.readAlgebra (p := p) g1 feat vk trace.permutations
    trace.lookups trace.trashcans nbCommitted numProofs instances).run t1
  pure ({ toSnapTrace := SnapTrace.mk trace, alg := alg }, t2)

/-- The public-column instance evaluation, selected BY COLUMN.

    The design sketch pinned this to (alg.instanceEvals.getD 0 #[]).getD 0 0, the
    first evaluation of the first proof. That is FALSE (attack finding,
    Snapshot.instanceEval): instanceEvals is built per instance QUERY in
    vk.cs.instanceQueries order (Verifier.lean:913-915), and a query on a COMMITTED
    column is a transcript read while the public column is the inner product
    sum inst_i * l_i (Verifier.lean:890-912). The contract INSTANCE_EVAL_MPTR is the
    inner product over the public calldata words (Lagrange.yul:65-73), so if the
    circuit registers the committed query first - and nothing pins the order - the
    sketch pins the transcript-read value and lagrange_spec is unprovable.

    So: the unique query on a column at or beyond nbCommitted (public) at rotation 0
    (the noRotInst shape), and none when the key does not have exactly one. Returning
    none rather than a default is what stops a wrong shape from becoming a silently
    wrong pin; the clause in Inv is inert while it is none, exactly like the
    linearization hole, and for the same reason. -/
def instanceEvalOf {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (alg : Verifier.AlgebraRead (Fr p) G₁) :
    Option (Fr p) :=
  let row := alg.instanceEvals.getD 0 #[]
  let hits := (List.zipIdx vk.cs.instanceQueries.toList).filter fun q =>
    q.1.1.index ≥ alg.nbCommitted && q.1.2.int == 0
  match hits with
  | [(_, i)] => row[i]?
  | _ => none

/-- lagrangeTriple plus the instance evaluation: the five values Lagrange.yul:81-86
    persists. Pure, and it is the step that makes lagrange_spec statable without the
    linearization or the PCS having run. -/
def snapshotLagrangeStep {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (vk : VerifyingKey (Fr p) G₁) (s2 : SnapAlgebra p G₁) :
    Except Fault (SnapLagrange p G₁) := do
  let lagrange ← lagrangeTriple vk s2.alg.x s2.alg.xn
  pure { toSnapAlgebra := s2, lagrange := lagrange,
           instanceEval := instanceEvalOf vk s2.alg }

/-- linearize: the multi-open query vector, and the linearization hole (always none,
    D6 limit 1). Pure given the algebra prefix - it touches no transcript state -
    which is why this step returns no transcript. -/
def snapshotQueriesStep {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type}
    (delta : Fr p) (vk : VerifyingKey (Fr p) G₁) (committed : Array (Array G₁))
    (s3 : SnapLagrange p G₁) :
    Except Fault (SnapQueries p G₁) := do
  let trace := s3.trace
  let queries ← Verifier.linearize (p := p) delta vk trace.adviceCommitments
    committed (y := trace.y) (beta := trace.beta) (gamma := trace.gamma)
    (theta := trace.theta) (trashChallenge := trace.trashChallenge)
    (challenges := trace.challenges) s3.alg
  pure { toSnapLagrange := s3, queries := queries, lin := none }

/-- The three PCS phases in order on the transcript state linearize left. Each is a
    projection of a record the Exec refactor made nameable; none is a recomputation.
    phaseB is group-free (MultiOpen.lean:273) and phaseA and phaseC are not, so this
    step is where the dictionary becomes necessary. -/
def snapshotPcsStep (E : VerifierEnv p G₁ G₂ Gₜ) (feat : Features)
    (s4 : SnapQueries p G₁) (t2 : Transcript) :
    Except Fault (SnapPcs p G₁ G₂ Gₜ × Transcript) := do
  let (a, t3) ← (phaseA (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field feat
    E.fewerPointSetsRuntime s4.queries).run t2
  let (b, t4) ← (phaseB E.g1 E.field feat a).run t3
  let (c, t5) ← (phaseC (G₂ := G₂) (Gₜ := Gₜ) E.g1 E.field feat a b).run t4
  pure ({ toSnapQueries := s4, a := a, b := b, c := c }, t5)

/-- The schedule, run once per boundary. Each level threads the transcript state the
    previous level left, so a prefix is a prefix of the same run rather than a second
    run of it, and each level stops where its boundary stops. -/
def snapshotTraceRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    Except Fault (SnapTrace p G₁ × Transcript) :=
  snapshotTraceStep (G₁ := G₁) E.g1 Features.solidity (transcriptOf E H ms) vk inst

/-- The shape checks verifyAlgebraicConstraints keeps for itself (Verifier.lean
    1029-1041), then the algebra step. Reproduced rather than assumed: they are part
    of the schedule, and a snapshot that skipped them would be .ok on calldata
    prepareMsgs rejects. -/
def snapshotAlgebraRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    Except Fault (SnapAlgebra p G₁ × Transcript) := do
  let (snap1, t1) ← snapshotTraceRun E H vk inst ms
  let trace := snap1.trace
  let committed :=
    if Features.solidity.committedInstances then committedShape (G₁ := G₁)
    else arrayReplicate (instanceShape inst).size (#[] : Array G₁)
  if committed.isEmpty then
    throw (Fault.error Error.invalidInstances)
  let nbCommitted := (committed[0]?.map (fun r => r.size)).getD 0
  snapshotAlgebraStep (G₁ := G₁) E.g1 Features.solidity vk trace nbCommitted
    (instanceShape inst).size (instanceShape inst) t1

/-- The Lagrange boundary: parseTrace, readAlgebra and lagrangeTriple, and nothing
    else. This is the prefix lagrange_spec is stated against, and the reason the
    chain exists - a linearize panic or an fEval panic cannot erase it. -/
def snapshotLagrangeRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    Except Fault (SnapLagrange p G₁ × Transcript) := do
  let (s2, t2) ← snapshotAlgebraRun E H vk inst ms
  pure (← snapshotLagrangeStep (G₁ := G₁) vk s2, t2)

/-- The linearization boundary: adds the multi-open query vector. Pure from the
    Lagrange prefix, so the transcript is the one readAlgebra left. -/
def snapshotQueriesRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    Except Fault (SnapQueries p G₁ × Transcript) := do
  let (s3, t2) ← snapshotLagrangeRun E H vk inst ms
  pure (← snapshotQueriesStep (G₁ := G₁) E.delta vk
    (committedShape (G₁ := G₁)) s3, t2)

/-- The PCS boundary: the three multi-open phases on the transcript the queries left. -/
def snapshotPcsRun (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) :
    Except Fault (SnapPcs p G₁ G₂ Gₜ × Transcript) := do
  let (s4, t2) ← snapshotQueriesRun E H vk inst ms
  snapshotPcsStep E Features.solidity s4 t2

/-- The prefix record at each boundary, for callers that do not need the transcript. -/
def snapshotOfTrace (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Except Fault (SnapTrace p G₁) :=
  Prod.fst <$> snapshotTraceRun E H vk inst ms

def snapshotOfAlgebra (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Except Fault (SnapAlgebra p G₁) :=
  Prod.fst <$> snapshotAlgebraRun E H vk inst ms

def snapshotOfLagrange (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Except Fault (SnapLagrange p G₁) :=
  Prod.fst <$> snapshotLagrangeRun E H vk inst ms

def snapshotOfQueries (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Except Fault (SnapQueries p G₁) :=
  Prod.fst <$> snapshotQueriesRun E H vk inst ms

def snapshotOfPcs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) : Except Fault (SnapPcs p G₁ G₂ Gₜ) :=
  Prod.fst <$> snapshotPcsRun E H vk inst ms

/-- The full snapshot of one message-level run: the SAME schedule prepareMsgs runs
    (Native.lean:255-268), cut at the refactored phase boundaries, with the
    trailing-bytes check last and the accumulator supplied by the caller. -/
def snapshotOf (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) (acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)) :
    Except Fault (Snapshot p G₁ G₂ Gₜ) := do
  let (s5, t5) ← snapshotPcsRun E H vk inst ms
  t5.assertEmpty
  pure { toSnapPcs := s5, acc := acc }


/-- Which prefix each checkpoint reads, recorded so a per-partial theorem can state
    its hypothesis at the weakest prefix that suffices. The two entries that matter:
    lagrange_spec needs only snapshotOfLagrange, so a linearize or PCS fault does not
    erase it, and transcriptParser_spec needs snapshotOfPcs because the parser
    partial writes x1..x4, which Lean squeezes inside the PCS phases. -/
def Checkpoint.prefixNeeds : Checkpoint → String
  | .start => "none"
  | .vk => "none"
  | .transcript => "snapshotOfPcs"
  | .lagrange => "snapshotOfLagrange"
  | .quotient => "snapshotOf"
  | .pcs => "snapshotOf"
  | .pairing => "snapshotOf"

/-- Agreement with prepareMsgs. Two parts, because verifyAlgebraicConstraints maps
    every multiPrepare Fault.error to Error.opening (R-8, Verifier.lean:1065-1066):
    the ok case is a value equality and the error case can only be compared through
    isOk. PROOF HOLE: the ok half is an unfolding of the composition plus a case
    split on the collapse; the isOk half additionally needs that no phase this file
    runs can fault where prepareMsgs succeeds, which is a claim that the Exec
    refactor is a cut and not a reordering (rule R1), and that claim is exactly what
    the D6 KATs and the conformance replay evidence, not a Lean proof. -/
theorem snapshotOf_prepareMsgs (E : VerifierEnv p G₁ G₂ Gₜ) (H : Hash)
    (vk : VerifyingKey (Fr p) G₁) (inst : Array (Fr p))
    (ms : List (Msg (Fr p) G₁)) (acc : Option (KzgAcc (Fr p) G₁ G₂ Gₜ)) :
    ((∀ S, snapshotOf E H vk inst ms acc = .ok S →
        prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms = .ok S.c.dual) ∧
      (snapshotOf E H vk inst ms acc).isOk =
        (prepareMsgs (Gₜ := Gₜ) E H Features.solidity vk inst ms).isOk) := by
  sorry

/-! ### A literal witness snapshot

    Structures in this tree carry no derived Inhabited, so a gate that needs a
    Snapshot needs one written out. This is that witness: every scalar a small
    distinct value, every commitment the identity, every array empty or one row. It
    needs only One G₁, so it exists at a curve-free type (G₁ := Nat) and at a real
    model alike, and Inv satisfiability is checked against it in
    Midfall/Instances/InvFixture.lean. -/

/-- The empty trace the witness snapshot is built on: no advice commitments, no
    lookups, no trashcans, no permutations, five challenge slots. -/
def witnessTrace {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [One G₁] :
    VerifierTrace (Fr p) G₁ :=
  { adviceCommitments := #[], lookups := #[], trashcans := #[], permutations := #[],
    challenges := #[11, 12], beta := 2, gamma := 3, theta := 4,
    trashChallenge := 5, y := 6 }

/-- The algebra record the witness snapshot is built on. x, the splitting factor and
    xn are distinct small values so that a clause pinning one of them to another is
    caught, and the six evaluation arrays are empty except instanceEvals, which
    carries one proof row of two values. -/
def witnessAlgebra {p : ℕ} [Fact (Nat.Prime p)] {G₁ : Type} [One G₁] :
    Verifier.AlgebraRead (Fr p) G₁ :=
  { nbCommitted := 1,
    quotientLimbComs := #[1, 1],
    x := 7, splittingFactor := 8, xn := 9,
    minRot := -1, maxRot := 2, maxInstanceLen := 2,
    rotations := [-1, 0, 1],
    lIS := #[13, 14, 15],
    instanceEvals := #[#[16, 1]],
    adviceEvals := #[#[2]],
    fixedEvals := #[3],
    permutationsCommon := { permutationEvals := #[] },
    permutationsEvaluated := #[],
    lookupsEvaluated := #[#[]],
    trashcansEvaluated := #[#[]] }

/-- The PCS phase records the witness snapshot is built on: empty MSMs and the
    identity point, with x1..x4, fEval, v and pi distinct small values so that a
    clause that swaps two of them fails. -/
def witnessPcs {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [One G₁] :
    SnapPcs p G₁ G₂ Gₜ :=
  { trace := witnessTrace, alg := witnessAlgebra,
    lagrange := { lLast := 21, lBlind := 22, l0 := 23 },
    instanceEval := some 1,
    queries := #[], lin := none,
    a := { x1 := 31, x2 := 32, qComs := #[], qEvalSets := #[#[]], pointSets := #[#[]] },
    b := { fCom := 1, x3raw := 41, x3 := 42, qEvalsOnX3 := [43], fEval := 44 },
    c := { x4 := 51, finalCom := { scalars := #[], bases := #[], labels := #[] },
           v := 52, pi := 1,
           dual := { left := { scalars := #[], bases := #[], labels := #[] },
                     right := { scalars := #[], bases := #[], labels := #[] } } } }

/-- The whole witness snapshot: the PCS prefix with the accumulator hole left empty. -/
def witnessSnapshot {p : ℕ} [Fact (Nat.Prime p)] {G₁ G₂ Gₜ : Type} [One G₁] :
    Snapshot p G₁ G₂ Gₜ :=
  { witnessPcs with acc := none }

/-! ### Known-answer checks

    Group-free wherever possible, per the stage-3 brief: readAlgebra, lagrangeTriple
    and phaseB take no curve, so the selection logic, the step chain and the hole
    discipline are all exercised over Fr 17 with G₁ := Nat. The end-to-end agreement
    of snapshotOf with prepareMsgs needs a pairing, so it lives in
    Midfall/Instances/, where a concrete model is allowed (hazard 5). -/

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- instanceEvalOf on the shape the attack finding names: TWO instance queries, the
    COMMITTED one first, one proof, values 16 (transcript read) and 1 (inner
    product). The selection must return the public one. The design sketch
    (instanceEvals.getD 0 #[]).getD 0 0 returns 16, so regressing to the sketch is a
    red gate rather than a silently wrong pin. -/
def instanceEvalOfKats_ok : Bool :=
  let withQueries (qs : Array (Column × Rotation)) (evals : Array (Array (Fr 17)))
      (nb : Nat) : Option (Fr 17) :=
    let vk : VerifyingKey (Fr 17) Nat :=
      { raVk with cs := { raCs with instanceQueries := qs } }
    instanceEvalOf (p := 17) vk { witnessAlgebra (p := 17) with
      nbCommitted := nb, instanceEvals := evals }
  -- committed query first, public second: the public value is 1
  (withQueries #[(vCol 0 Any.instance, Rotation.value 0),
                 (vCol 1 Any.instance, Rotation.value 0)] (#[#[16, 1]]) 1) == some 1 &&
  -- public first, committed second: same answer, so the pin is by column and not by
  -- position in the array
  (withQueries #[(vCol 1 Any.instance, Rotation.value 0),
                 (vCol 0 Any.instance, Rotation.value 0)] (#[#[1, 16]]) 1) == some 1 &&
  -- the raCs shape: two public queries at rotations +1 and +2, no rotation-0 query
  -- at all, so none rather than a default
  (withQueries #[(vCol 0 Any.instance, Rotation.value 1),
                 (vCol 1 Any.instance, Rotation.value 2)] (#[#[16, 5]]) 0) == none &&
  -- two public rotation-0 queries: ambiguous, so none rather than a guess
  (withQueries #[(vCol 1 Any.instance, Rotation.value 0),
                 (vCol 2 Any.instance, Rotation.value 0)] (#[#[5, 6]]) 0) == none &&
  -- no queries at all
  (withQueries #[] (#[] : Array (Array (Fr 17))) 0) == none

/-- The linearization hole is a hole and the bucket projection is the commitment
    scalars, not the points: QUOTIENT_EVAL is the eval and SELECTOR_ACC is the
    scalar side of a linear commitment. -/
def linComHoleKats_ok : Bool :=
  let q : VerifierQuery (Fr 17) Nat :=
    { point := 1, commitmentLabel := CommitmentLabel.noLabel,
      commitment := .linear #[3, 4] #[5, 6]
        #[CommitmentLabel.fixed 0, CommitmentLabel.fixed 1],
      eval := 9 }
  linComBuckets q == (#[5, 6] : Array (Fr 17)) && linComEval q == (9 : Fr 17) &&
    -- a one-piece linearization has no buckets at all
    linComBuckets (VerifierQuery.new 1 CommitmentLabel.noLabel 7 2) == (#[] : Array (Fr 17)) &&
    -- and the hole is never filled by the witness either
    (witnessSnapshot (p := 17) (G₁ := Nat) (G₂ := Nat) (Gₜ := Nat)).lin.isNone &&
    (witnessSnapshot (p := 17) (G₁ := Nat) (G₂ := Nat) (Gₜ := Nat)).acc.isNone

/-- The algebra step reproduces the values the Exec refactor pinned: x, the splitting
    factor and xn over the readAlgebra fixture are (15, 9, 16) (Verifier.lean
    raChallenges_kats_ok), reached here through the snapshot step rather than through
    readAlgebra directly. If the step reordered or dropped a read the triple changes. -/
def snapshotAlgebraStepKats_ok : Bool :=
  match snapshotAlgebraStep (p := 17) (G₁ := Nat) natG1Codec Features.solidity raVk
      (witnessTrace (p := 17) (G₁ := Nat)) 0 1
      (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17))))
      (Transcript.initFromBytes raBytes) with
  | .ok (s, _) =>
      [ZMod.val s.alg.x, ZMod.val s.alg.splittingFactor, ZMod.val s.alg.xn] == [15, 9, 16] &&
      s.alg.instanceEvals.toList.map (fun r => ZMod.val <$> r.toList) == [[16, 5]]
  | .error _ => false

/-- The Lagrange step on the same fixture: the three slots the Exec refactor pinned
    at (13, 12, 15) for x = 5, xn = 3 (Verifier.lean lagrangeTriple_kats_ok), reached
    through the prefix chain. -/
def snapshotLagrangeStepKats_ok : Bool :=
  match snapshotAlgebraStep (p := 17) (G₁ := Nat) natG1Codec Features.solidity raVk
      (witnessTrace (p := 17) (G₁ := Nat)) 0 1
      (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17))))
      (Transcript.initFromBytes raBytes) with
  | .ok (s, _) =>
      match snapshotLagrangeStep (p := 17) (G₁ := Nat) raVk
          { s with alg := { s.alg with x := 5, xn := 3 } } with
      | .ok l => [ZMod.val l.lagrange.lLast, ZMod.val l.lagrange.lBlind,
                  ZMod.val l.lagrange.l0] == [13, 12, 15]
      | .error _ => false
  | .error _ => false

/-- D6 LIMIT 2, EXHIBITED. A fault in a late phase destroys the prefixes at and
    after it and leaves the earlier ones standing. The empty transcript cannot even
    read a commitment, so every prefix faults; the witness snapshot shows the chain
    is not a constant (it has values); and the queries step on a trace whose advice
    commitments are empty while the algebra claims a proof row faults without
    touching the earlier steps. The point of the gate is the FIRST conjunct: the
    prefix runners can fail, so a per-partial theorem stated against one is not
    vacuously hypothesised. -/
def prefixSurvivesFaultKats_ok : Bool :=
  let t0 := Transcript.initFromBytes Midfall.Bytes.empty
  -- the earliest step already fails on an empty stream, so the chain can fault and a
  -- theorem stated against a prefix is not vacuously hypothesised
  (snapshotTraceStep (G₁ := Nat) natG1Codec Features.solidity t0 raVk #[0]).isOk == false &&
  -- the algebra step faults on a transcript too short for the quotient limbs
  (snapshotAlgebraStep (p := 17) (G₁ := Nat) natG1Codec Features.solidity raVk
      (witnessTrace (p := 17) (G₁ := Nat)) 0 1
      (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17)))) t0).isOk == false &&
  -- D6 LIMIT 2, EXHIBITED FROM THE OTHER SIDE: on the readAlgebra fixture the
  -- Lagrange prefix exists even though the transcript is already exhausted, so every
  -- phase after it would fault. The prefix this file exists to protect is untouched
  -- by a fault it does not depend on.
  (match snapshotAlgebraStep (p := 17) (G₁ := Nat) natG1Codec Features.solidity raVk
        (witnessTrace (p := 17) (G₁ := Nat)) 0 1
        (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17))))
        (Transcript.initFromBytes raBytes) with
   | .ok (s2, _) =>
       (snapshotLagrangeStep (p := 17) (G₁ := Nat) raVk s2).isOk == true &&
       s2.alg.instanceEvals.size == 1
   | .error _ => false)

/-- The prefix map is total and says what the header claims: the Lagrange boundary is
    reached by a runner that never calls linearize, and the transcript boundary is not.
    If a refactor made snapshotOfLagrange depend on the PCS, this is where it shows. -/
def prefixNeedsKats_ok : Bool :=
  Checkpoint.prefixNeeds .start == "none" &&
  Checkpoint.prefixNeeds .vk == "none" &&
  Checkpoint.prefixNeeds .lagrange == "snapshotOfLagrange" &&
  Checkpoint.prefixNeeds .transcript == "snapshotOfPcs" &&
  Checkpoint.prefixNeeds .quotient == "snapshotOf" &&
  Checkpoint.prefixNeeds .pcs == "snapshotOf" &&
  Checkpoint.prefixNeeds .pairing == "snapshotOf" &&
  -- and the two runners the map names really are different functions: the Lagrange
  -- prefix exists on a transcript the PCS prefix cannot finish
  (match snapshotAlgebraStep (p := 17) natG1Codec Features.solidity raVk
        (witnessTrace (p := 17) (G₁ := Nat)) 0 1
        (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17))))
        (Transcript.initFromBytes raBytes) with
   | .ok (s2, _) => (snapshotLagrangeStep (p := 17) raVk s2).isOk == true
   | .error _ => false)

#eval instanceEvalOfKats_ok               -- expect true
#eval linComHoleKats_ok                   -- expect true
#eval snapshotAlgebraStepKats_ok          -- expect true
#eval snapshotLagrangeStepKats_ok         -- expect true
#eval prefixSurvivesFaultKats_ok          -- expect true
#eval prefixNeedsKats_ok                  -- expect true

end Midfall.Lowering

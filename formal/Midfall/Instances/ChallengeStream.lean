-- |
-- Midfall.Instances.ChallengeStream
--
-- The challenge-stream gate for the P-D6 Exec refactor
-- (docs/plans/P-D6-exec-refactor.md, P-SE decision D6). Read this file as the answer
-- to a question the D6 gate as originally written could not ask: the agreed safety
-- gate was "every existing `#eval ... -- expect` token in Verifier.lean,
-- MultiOpen.lean and Native.lean stays identical", and two of those three files have
-- NO tokens at all. MultiOpen.lean is the file whose refactor moves FOUR transcript
-- squeezes - x1, x2, x3raw plus the truncatedChallenges branch that turns it into x3,
-- then x4 - and it had zero KATs. A refactor that swapped two squeezes or dropped the
-- truncation would have passed that gate while changing the Fiat-Shamir schedule and
-- therefore the whole protocol. That is docs/REVIEW.md R-41: a gate that cannot fail
-- is not a gate.
--
-- WHAT EACH GATE PINS, AND WHY IT IS THE RIGHT OBSERVABLE.
--
-- `multiPrepare` returns only a `DualMSM`, so the challenges are not directly
-- observable from it. They are observable in three places, and the three are
-- deliberately different in what they can see:
--
-- * the transcript `log` and `pos`: the widths of the reads, in order. This sees a
--   reordered or dropped READ, and it sees a squeeze that was added or removed, but
--   NOT a swap of two consecutive squeezes (nothing is absorbed between x1 and x2, so
--   the digest chain is identical).
-- * the transcript `state` after the run, whose first 32 bytes are the digest the x4
--   squeeze produced: that digest is a hash over the whole absorb/squeeze
--   interleaving, so it pins the schedule end to end. Same caveat: it cannot see an
--   x1/x2 swap, which is why the third observable is needed.
-- * the `DualMSM` itself. Its right channel literally CARRIES x3 and v as the last
--   two scalars (kzg/mod.rs:544-551 puts `scalars := #[x3, v]` over
--   `bases := #[pi, -G]`), and the earlier scalars are the truncated powers of x4
--   folded into the q_i combinations, while its bases carry the x1 powers folded by
--   `buildQ`. So an x1/x2 swap moves the bases, and dropping the x3 truncation moves
--   the fourth scalar. This is the observable that closes the gap the other two leave.
--
-- WHY THIS FILE IS UNDER Instances/ AND NOT INSIDE Exec/Kzg/MultiOpen.lean, which is
-- where the brief asked for the gates. An executable challenge-stream gate has to
-- instantiate `multiPrepare` at a concrete `AdmissiblePairing`, and the only one in
-- the tree is `Midfall/Instances/ExponentModel.lean` (R-28). `ExponentModel` imports
-- `Exec.Pcs`, which imports `Exec.Kzg.MultiOpen`, so the dependency can only run this
-- way: MultiOpen importing the model is an import cycle, and Native importing it would
-- put a concrete model inside the transitive cone of `Midfall/Statements.lean` and
-- `Midfall/Lowering/*`, which is exactly what D-P17 and the "Instances/ import
-- confinement" gate in scripts/checks.sh exist to prevent (and the confinement check
-- only looks at DIRECT imports, so it would NOT have caught that). The gates therefore
-- live beside the model, and scripts/checks.sh runs them through the same
-- kat_gate.py as every other KAT in the tree. What the two Exec files gained instead
-- is the pairing-free half of the pin (Exec/Kzg/MultiOpen.lean's own KAT section:
-- fEval, vCalc, sortById and the truncation branch), which is where the challenge
-- VALUES are consumed and where a dropped truncation is visible without a curve.
--
-- NOTHING HERE IS A PROOF. Bool computations, in the style of ExponentModel and
-- NativeE2E; the model is a model of exponent arithmetic, not of BLS12-381 (R-33).
-- The expected values were measured against the PRE-REFACTOR monolithic bodies at
-- git HEAD, which is the point: they pin what the code does now so that the split in
-- stages 3 and 4 has something to break.

import Midfall.Halo2.Exec.Kzg.MultiOpen
import Midfall.Halo2.Exec.Verifier
import Midfall.Assumptions.TwoAdicity
import Midfall.Instances.ExponentModel
import Midfall.Instances.NativeE2E

namespace Midfall.Instances.ChallengeStream

open Midfall Midfall.Halo2 Midfall.Instances

local instance fact17cs : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Everything a run leaves behind: the guard's two channels in decidable form, plus
    the transcript observables. `none` from a run means it faulted, and every gate
    below treats that as a failure rather than as a value. -/
structure Obs where
  /-- `DualMSM.left.scalars`, as field-element values. -/
  lsc : List Nat
  /-- `DualMSM.left.bases`, as exponents in the model. -/
  lbas : List Nat
  /-- `DualMSM.left.labels`, as the Rust `Display` strings. -/
  llab : List String
  /-- `DualMSM.right.scalars`. The last two are x3 and v (kzg/mod.rs:544-551). -/
  rsc : List Nat
  /-- `DualMSM.right.bases`. The last two are pi and -G. -/
  rbas : List Nat
  /-- `DualMSM.right.labels`. -/
  rlab : List String
  /-- Transcript cursor position after the run. -/
  pos : Nat
  /-- The wire width of every read, in order: the read schedule. -/
  log : List Nat
  /-- The first 32 bytes of the final transcript state, i.e. the digest the LAST
      squeeze produced (x4) - the squeeze schedule, hashed. -/
  digest : Nat
  /-- `DualMSM.check` against `expPrm`. -/
  check : Bool
  deriving BEq

/-- Encode (wire width, value) slots the way the transcript reads them: a G1 point is
    48 big-endian bytes, a scalar 32 little-endian bytes. Same convention as
    `NativeE2E.n2Bytes`. -/
def csBytes (slots : List (Nat × Nat)) : Bytes :=
  slots.foldl (init := Bytes.empty) fun acc s =>
    ByteArray.append acc
      (if s.1 == g1CompressedWidth then natToBytesBE s.2 g1CompressedWidth
       else natToBytesLE s.2 32)

/-- Project a finished run down to the observables. -/
def csObs (d : DualMSM (Fr 17) (Exp 17) (Exp 17) (Exp 17)) (t : Transcript) : Obs :=
  { lsc := d.left.scalars.toList.map ZMod.val,
    lbas := d.left.bases.toList.map expOf,
    llab := d.left.labels.toList.map CommitmentLabel.text,
    rsc := d.right.scalars.toList.map ZMod.val,
    rbas := d.right.bases.toList.map expOf,
    rlab := d.right.labels.toList.map CommitmentLabel.text,
    pos := t.pos,
    log := t.log.toList.map Prod.fst,
    digest := bytesToNatBE (t.state.extract 0 32),
    check := DualMSM.check d expPrm }

/-! ## 1. The `multiPrepare` fixture: five queries, two point sets, four squeezes -/

/-- The three point-set members the KZG read schedule needs. `zA`/`zB` are shared by
    two commitments, so `nbX1Powers = 2` and the x1 powers are load-bearing; `zC` is
    opened alone, so the ascending-cardinality permutation in `buildQ`
    (kzg/mod.rs:409-424) actually moves a set. -/
def zA : Fr 17 := 3

/-- The second opening point of the two shared commitments. -/
def zB : Fr 17 := 5

/-- The singleton point set's point. -/
def zC : Fr 17 := 11

/-- The query vector. Two commitments (`ex 11`, `ex 12`) are opened at both `zA` and
    `zB`, and a third (`ex 13`) only at `zC`, so `constructIntermediateSets` yields
    point sets `[[zA, zB], [zC]]` and `buildQ` permutes them to `[[zC], [zA, zB]]`.
    The linearization-style query is the singleton, labelled `custom "lin"`. -/
def mpQueries : Array (VerifierQuery (Fr 17) (Exp 17)) :=
  #[ VerifierQuery.new zA (CommitmentLabel.advice 0) (ex 11) 2,
     VerifierQuery.new zB (CommitmentLabel.advice 1) (ex 11) 3,
     VerifierQuery.new zA (CommitmentLabel.fixed 0) (ex 12) 4,
     VerifierQuery.new zB (CommitmentLabel.fixed 1) (ex 12) 5,
     VerifierQuery.new zC (CommitmentLabel.custom "lin") (ex 13) 6 ]

/-- The proof stream `multiPrepare` consumes: `f_com` (kzg/mod.rs:447), the two
    `q_evals_on_x3` (one per point set, :461-467) and `pi` (:531). -/
def mpSlots (pi : Nat) : List (Nat × Nat) :=
  [(48, 6), (32, 7), (32, 8), (48, pi)]

/-- Run `multiPrepare` on the fixture at a candidate `pi`, with a chosen
    `f_com` exponent so the non-vacuity gate can move an absorbed byte. -/
def mpRunAt (fCom pi : Nat) : Option Obs :=
  match (multiPrepare (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17)
      expG1Codec fc17 Features.solidity false mpQueries).run
      (Transcript.initFromBytes (csBytes ([(48, fCom)] ++ (mpSlots pi).tail!))) with
  | .ok (d, t) => some (csObs d t)
  | .error _ => none

/-- Run `multiPrepare` on the pinned fixture. -/
def mpRun (pi : Nat) : Option Obs := mpRunAt 6 pi

/-- The accepting pi for this fixture: found by searching all seventeen exponents,
    because in the exponent model the final equation is linear in pi (R-28). -/
def mpPi : Nat := 3

/-- THE READ/SQUEEZE INTERLEAVING. `f_com` is read BEFORE x3 is squeezed and the
    `q_evals_on_x3` block AFTER it (kzg/mod.rs:447 then :455 then :461) - the order
    the doc comment at the top of MultiOpen.lean calls the Fiat-Shamir schedule.
    Moving any of those four reads, or inserting a squeeze, changes either this list
    or the digest below. -/
def mpReadSchedule_ok : Bool :=
  match mpRun mpPi with
  | some o => o.log == [48, 32, 32, 48] && o.pos == 160
  | none => false

/-- THE SQUEEZE SCHEDULE, HASHED. This 256-bit digest is the transcript state the x4
    squeeze produced, so it is keccak over everything absorbed before it: x1, x2, the
    absorbed `f_com`, x3, the absorbed `q_evals_on_x3`. Reordering the reads around
    the squeezes, or squeezing a different number of times, moves it. It is
    deliberately INSENSITIVE to pi (pi is absorbed after x4) and to an x1/x2 swap
    (nothing is absorbed between them) - `mpRightChannel_ok` is what covers those. -/
def mpDigest_ok : Bool :=
  (mpRun mpPi).map (fun o => o.digest)
    == some 49088159298228319465952213363062635645734396069589306369751284586999767722300

/-- THE RIGHT CHANNEL, which is where the challenges become visible. Read the five
    scalars against kzg/mod.rs:488-516: the first three are the (truncated) powers of
    x4 folded into `[q_0, q_1, f_com]` by `finalCom`, and the last two are `x3` and
    `v` from `scaled_pi`. So the fourth scalar IS x3 - the value the
    `truncatedChallenges` branch produces at MultiOpen.lean:228 - and the fifth is
    `v`, an inner product over the same truncated x4 stream. The bases pin x1:
    `[13, 9, ...]` are the q_i combinations after `buildQ` scaled them by the powers
    of x1, so swapping x1 and x2 moves them. -/
def mpRightChannel_ok : Bool :=
  match mpRun mpPi with
  | some o =>
      o.rsc == [1, 6, 2, 10, 12] &&
      o.rbas == [13, 9, 6, mpPi, 16] &&
      o.rlab == ["lin", "-", "-", "π", "-G"]
  | none => false

/-- THE LEFT CHANNEL: `[1] · pi` with the `custom "π"` label (kzg/mod.rs:527-533).
    Pinned separately because the left channel is the one place a swapped `addMsm`
    result would show up as a change here rather than on the right. -/
def mpLeftChannel_ok : Bool :=
  match mpRun mpPi with
  | some o => o.lsc == [1] && o.lbas == [mpPi] && o.llab == ["π"]
  | none => false

/-- THE GUARD IS THE ONE THAT ACCEPTS. Exactly one of the seventeen candidate pis
    balances the pairing equation, and it is the one pinned above. A reorder that
    moved a squeeze past a read would shift every challenge and destroy this. -/
def mpAccept_ok : Bool :=
  (List.range 17).filter (fun pi => (mpRun pi).map (fun o => o.check) == some true)
    == [mpPi]

/-- NON-VACUITY. The pins above are all equalities against measured constants, so
    the failure mode to rule out is a `multiPrepare` that ignores its transcript.
    Changing one absorbed byte (`f_com` 6 -> 7) must change the digest AND the right
    channel; if it changed neither, the schedule pins would be vacuous. -/
def mpNonVacuous_ok : Bool :=
  match mpRun mpPi, mpRunAt 7 mpPi with
  | some o, some o2 => o.digest ≠ o2.digest && o.rsc ≠ o2.rsc && o2.check == false
  | _, _ => false

/-! ## 1b. The x3 TRUNCATION gate, at a prime where truncation is not the identity

    Hazard 2 of the brief: the x3 truncation is a feature branch INSIDE the squeeze
    sequence (`let x3 := if feat.truncatedChallenges then truncate fc.numBits x3raw
    else x3raw`, MultiOpen.lean:228), and R-22/D-P14 make truncated-challenges the
    deployed profile. It cannot be gated at `Fr 17`: `truncate` keeps
    `divCeil (divCeil numBits 8) 2` = 1 byte and every element of `Fr 17` is below
    256, so truncation is the identity there and a gate that dropped the branch would
    still pass. `Fr 1009` is the smallest useful prime above 256 for the same
    `numBits`, and the fixture below is chosen so that the squeezed x3 is 744 - above
    256 - so the truncated value is 232 and the two are visibly different. Dropping the
    branch moves the pinned 232 to 744 and reddens `mpTruncX3_ok`. -/

set_option maxRecDepth 100000 in
local instance fact1009cs : Fact (Nat.Prime 1009) := ⟨by decide⟩

/-- `Fr 1009` with the truncation width the gate needs - one byte - and field constants
    that are TRUE. P-ENV repaired `rootOfUnity`, `zeta` and `numBits` here: the site reads
    only `fc.numBits` (MultiOpen.lean:131, :181, :191, :281), so the three order-bearing
    fields were unread and therefore unfalsifiable, and they were the ZMod-17-shaped
    placeholder `rootOfUnity := 3, zeta := 2` that P-4a2 PROVED fails both halves of
    `FieldConsts.IsWellFormed` (`TwoAdicity.fc1009Placeholder_root_fails`,
    `..._zeta_fails`: 3 has order 168 mod 1009 and 2 has order 504). The values now are
    `Midfall.Assumptions.fc1009Real`, whose well-formedness is a kernel theorem
    (`fc1009Real_isWellFormed`, discharged below at THIS name). `numBits` moves 5 -> 10,
    the true bit width of 1009, and the truncation width is unchanged because
    divCeil (divCeil 5 8) 2 = 1 = divCeil (divCeil 10 8) 2 - which is why every pinned
    value in this section is the same value it was before the repair, and why no
    expectation had to be re-derived. -/
def fc1009 : FieldConsts (Fr 1009) :=
  { numBits := 10, s := 4, rootOfUnity := 62, zeta := 374 }

/-- THE REPAIRED CONSTANTS ARE WELL FORMED, as a theorem and not as a comment: root of
    order exactly 2^4, zeta of order exactly 3, s < numBits. The proof is the kernel
    exhibit in `Midfall/Assumptions/TwoAdicity.lean`, and it typechecks here only because
    this `fc1009` has the same three values - put the placeholder back and this line is a
    build failure, which is the falsifiability half. -/
theorem fc1009_isWellFormed : fc1009.IsWellFormed :=
  Midfall.Assumptions.fc1009Real_isWellFormed

def ex9 (n : Nat) : Exp 1009 := Multiplicative.ofAdd (n : ZMod 1009)

def expOf9 (x : Exp 1009) : Nat := x.toAdd.val

/-- The same five-query shape as section 1, over `Fr 1009`. -/
def mp9Queries : Array (VerifierQuery (Fr 1009) (Exp 1009)) :=
  #[ VerifierQuery.new 3 (CommitmentLabel.advice 0) (ex9 11) 2,
     VerifierQuery.new 5 (CommitmentLabel.advice 1) (ex9 11) 3,
     VerifierQuery.new 3 (CommitmentLabel.fixed 0) (ex9 12) 4,
     VerifierQuery.new 5 (CommitmentLabel.fixed 1) (ex9 12) 5,
     VerifierQuery.new 11 (CommitmentLabel.custom "lin") (ex9 13) 6 ]

/-- `f_com` = 7 and the first `q_evals_on_x3` = 0 are chosen so that the squeezed x3
    is 744, i.e. above 256, so the truncation actually bites. -/
def mp9Run (feat : Features) (pi : Nat) : Option (List Nat × List Nat × List String) :=
  match (multiPrepare (p := 1009) (G₂ := Exp 1009) (Gₜ := Exp 1009)
      expG1Codec fc1009 feat false mp9Queries).run
      (Transcript.initFromBytes (csBytes [(48, 7), (32, 0), (32, 800), (48, pi)])) with
  | .ok (d, _) => some (d.right.scalars.toList.map ZMod.val,
                        d.right.bases.toList.map expOf9,
                        d.right.labels.toList.map CommitmentLabel.text)
  | .error _ => none

/-- THE TRUNCATION GATE. The fourth right-channel scalar is x3, and it is 232 - the
    truncated value - not 744. -/
def mpTruncX3_ok : Bool :=
  (mp9Run Features.solidity 1).map (fun o => o.1) == some [1, 92, 24, 232, 586]

/-- The raw and truncated values really differ here, so the gate above is not pinned to
    a constant the branch cannot change: truncate 5 of 744 is 232 and 232 is not 744. -/
def mpTruncBites_ok : Bool :=
  ZMod.val (truncate (p := 1009) 5 (744 : Fr 1009)) == 232 && (232 : Nat) ≠ 744

/-- And the whole right channel moves with the branch: the same fixture with
    `truncatedChallenges` off gives a different guard, so a refactor that dropped the
    branch would be caught by a right-channel pin too, not only by `mpTruncX3_ok`. -/
def mpTruncChangesGuard_ok : Bool :=
  match mp9Run Features.solidity 1,
        mp9Run { Features.solidity with truncatedChallenges := false } 1 with
  | some a, some b => a.1 ≠ b.1 && a.1 == [1, 92, 24, 232, 586] &&
                      b.1 ≠ [1, 92, 24, 232, 586]
  | _, _ => false


/-! ## 2. The `verifyAlgebraicConstraints` fixture: positive instance rotations -/

/-- The gate that USES the public instance column: `q_fixed(0) * advice(0) + inst(1)`.
    The `Expression.instance` term is what makes the Lagrange window load-bearing -
    `instanceColumn` reads `instance_evals[q.index]` (plonk/mod.rs:535), and the
    public column's evaluation is the inner product of the instance values against
    the `l_i_s` window. With a gate that ignores instances (the shape the earlier
    fixtures use) the whole `rotations`/`lIS` block is unobservable from the output,
    which is why hazard 3 needs this fixture rather than the existing ones. -/
def algGateAt (rot1 : Int) : Gate (Fr 17) :=
  { name := "g", constraintNames := #["c"],
    polys := #[Expression.sum
      (Expression.product
        (Expression.fixed { index := some 0, columnIndex := 0, rotation := .cur })
        (Expression.advice { index := some 0, columnIndex := 0, rotation := .cur,
                             phase := ⟨0⟩ }))
      (Expression.instance { index := some 1, columnIndex := 1,
                             rotation := Rotation.value rot1 })],
    queriedSelectors := #[{ index := 0, isSimple := true }], queriedCells := #[] }

/-- The same constraint system with a given pair of instance rotations: the knob the
    window-sensitivity gate turns. Both instance columns are PUBLIC (`committed` is
    empty below), so neither instance query reaches the multi-open query vector and
    the rotations can be changed WITHOUT touching the read schedule. The pinned pair
    is +1 and +2, i.e. strictly positive: this is the all-positive query set hazard 3
    names. `rotBounds` (verifier.rs:330-339, ported at Verifier.lean:848-851) is an
    if / ELSE IF fold seeded with `(0, 0)`, so `minRot` stays 0 and is NOT the
    smallest positive rotation; the window is `-maxRot .. maxInstanceLen + |minRot|`
    = `-2 .. 2`. Kept as written, and `algRotWindow_ok` is the gate that would fail if
    someone "fixed" it during the move. -/
def algCsRot (rot0 rot1 : Int) : ConstraintSystem (Fr 17) :=
  { n2Cs with
    gates := #[algGateAt rot1],
    instanceQueries := #[({ index := 0, columnType := Any.instance }, Rotation.value rot0),
                          ({ index := 1, columnType := Any.instance }, Rotation.value rot1)] }

/-- The pinned constraint system: rotations +1 and +2. -/
def algCs : ConstraintSystem (Fr 17) := algCsRot 1 2

def algVk : VerifyingKey (Fr 17) (Exp 17) := { n2Vk with cs := algCs }

/-- The proof stream: advice commitment, the two quotient limbs, the advice
    evaluation, `f_com`, one `q_evals_on_x3` (one point set: every query is at `x`),
    then pi. No committed-instance read, because `committed` has no columns. -/
def algSlots (pi : Nat) : List (Nat × Nat) :=
  [(48, 3), (48, 1), (48, 2), (32, 5), (48, 6), (32, 4), (48, pi)]

/-- `Verifier.prepare` on a key, with the schedule observables. `prepare` is
    `parseTrace` + `verifyAlgebraicConstraints`, so this pins the whole Fiat-Shamir
    schedule of the algebraic half too. -/
def algRunOn (vk : VerifyingKey (Fr 17) (Exp 17)) (pi : Nat) : Option Obs :=
  match (Verifier.prepare (p := 17) expG1Codec 2 Features.solidity
        (Pcs.kzg (p := 17) expG1Codec fc17 Features.solidity false) vk
        (#[#[]] : Array (Array (Exp 17)))
        (#[#[#[3, 5], #[7]]] : Array (Array (Array (Fr 17))))).run
      (Transcript.initFromBytes (csBytes (algSlots pi))) with
  | .ok (d, t) => some (csObs d t)
  | .error _ => none

/-- The accepting pi for the algebraic fixture. -/
def algPi : Nat := 11

/-- The full read schedule of the algebraic half plus the KZG half: advice, the two
    quotient limbs, the advice evaluation, `f_com`, `q_evals_on_x3`, `pi`. -/
def algReadSchedule_ok : Bool :=
  match algRunOn algVk algPi with
  | some o => o.log == [48, 48, 48, 32, 48, 32, 48] && o.pos == 304
  | none => false

/-- The digest the x4 squeeze produced, i.e. the whole Fiat-Shamir schedule of
    `verify_algebraic_constraints` followed by `multi_prepare`: VK, committed
    instances and lengths, beta, gamma, theta, y, the challenges, the quotient limbs,
    x, the instance and advice and fixed evaluations, then x1, x2, f_com, x3, the
    q_evals, x4. Any squeeze moved anywhere in either half changes it. -/
def algDigest_ok : Bool :=
  (algRunOn algVk algPi).map (fun o => o.digest)
    == some 102061851421284688730508941961897436949496449066978522211995546848800112401783

/-- The linearization query list, as the guard records it. The seven right-channel
    bases are the multi-open query vector folded by `buildQ` and `finalCom`:
    `advice_0`, the two quotient limbs, `fixed_0`, `f_com`, `pi`, `-G`. The fourth
    scalar (7) is x3 and the sixth (14) is v. The instance inner products ride on the
    linearization term, which is what makes the window observable. -/
def algDual_ok : Bool :=
  match algRunOn algVk algPi with
  | some o =>
      o.lsc == [1] && o.lbas == [algPi] && o.llab == ["π"] &&
      o.rsc == [1, 14, 8, 7, 12, 16, 14] &&
      o.rbas == [3, 1, 2, 7, 6, algPi, 16] &&
      o.rlab == ["advice_0", "-", "-", "fixed_0", "-", "π", "-G"]
  | none => false

/-- Exactly one candidate pi accepts. -/
def algAccept_ok : Bool :=
  (List.range 17).filter (fun pi => (algRunOn algVk pi).map (fun o => o.check) == some true)
    == [algPi]

/-- HAZARD 3'S GATE: the rotation window is load-bearing. Three rotation profiles give
    three different guards, so `rotBounds`, `windowStart`/`windowStop`, `rotations`
    and `lIS` all reach the output. In particular the (0,0)-seeded `minRot` is what
    makes the window `-2 .. 2` here; seeding the fold with the first rotation instead
    (the "obvious fix" the brief forbids) changes `absMin`, hence `windowStop`, hence
    the slice, hence the instance inner product, hence the scalar pinned below. -/
def algRotWindow_ok : Bool :=
  match algRunOn { algVk with cs := algCsRot 1 2 } algPi,
        algRunOn { algVk with cs := algCsRot 0 0 } algPi,
        algRunOn { algVk with cs := algCsRot 2 1 } algPi with
  | some a, some b, some c =>
      a.rsc ≠ b.rsc && a.rsc ≠ c.rsc && b.rsc ≠ c.rsc &&
      a.rsc == [1, 14, 8, 7, 12, 16, 14] && b.rsc == [1, 14, 8, 8, 12, 16, 14]
  | _, _, _ => false

/-- The digest must NOT move when only the algebraic window moves: the two fixtures
    above differ in the guard but share the schedule. That is what separates the two
    halves of the pin - a refactor that moved a squeeze would change this, a refactor
    that changed the window would not. -/
def algDigestScheduleOnly_ok : Bool :=
  (algRunOn { algVk with cs := algCsRot 0 0 } algPi).map (fun o => o.digest)
    == (algRunOn algVk algPi).map (fun o => o.digest)

/-- The window really is the (0,0)-seeded one: the pinned profile's instance
    evaluation is the inner product of `[7]` against `l_i_s[0..1]`, and the
    all-zero-rotation profile's is against `l_i_s[0..1]` of a DIFFERENT window. The
    two differ, which is only possible because `maxRot` moved. Recorded as a separate
    gate so a failure names the window rather than the guard. -/
def algWindowMoved_ok : Bool :=
  match algRunOn { algVk with cs := algCsRot 1 2 } algPi,
        algRunOn { algVk with cs := algCsRot 1 1 } algPi with
  | some a, some b => a.rsc ≠ b.rsc
  | _, _ => false


/-- R-8'S LOCALITY, part 1: a proof truncated exactly where multiPrepare starts
    (parseTrace has consumed 208 bytes: advice, two quotient limbs, the committed
    instance evaluation and the advice evaluation) makes the KZG f_com read fail with
    Transcript(UnexpectedEof) - and verify_algebraic_constraints COLLAPSES that to
    Error::Opening at verifier.rs:651. The doc comment there is explicit that the
    collapse is local and must not be "improved", so it is pinned: a refactor that
    dropped the collapse would report "eof" here. -/
def algR8Collapsed_ok : Bool :=
  match (Verifier.prepare (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17) expG1Codec 2
        Features.solidity
        (Pcs.kzg (G₂ := Exp 17) (Gₜ := Exp 17) (p := 17) expG1Codec fc17
          Features.solidity false) n2Vk
        (#[#[1]] : Array (Array (Exp 17)))
        (#[#[#[0, 1]]] : Array (Array (Array (Fr 17))))).run
      (Transcript.initFromBytes ((n2Proof n2Pi).extract 0 208)) with
  | .error (Fault.error Error.opening) => true
  | _ => false

/-- R-8'S LOCALITY, part 2: the same truncation one read earlier, inside parseTrace,
    must NOT be collapsed - it fails as Transcript(UnexpectedEof), because the map_err
    sits on the multi_prepare call and nowhere else. Without this second half the first
    one would be satisfied by a blanket collapse, which is the "improvement" R-8
    forbids. -/
def algR8NotCollapsed_ok : Bool :=
  match (Verifier.prepare (p := 17) (G₂ := Exp 17) (Gₜ := Exp 17) expG1Codec 2
        Features.solidity
        (Pcs.kzg (G₂ := Exp 17) (Gₜ := Exp 17) (p := 17) expG1Codec fc17
          Features.solidity false) n2Vk
        (#[#[1]] : Array (Array (Exp 17)))
        (#[#[#[0, 1]]] : Array (Array (Array (Fr 17))))).run
      (Transcript.initFromBytes ((n2Proof n2Pi).extract 0 200)) with
  | .error (Fault.error (Error.transcript IoErrorKind.unexpectedEof)) => true
  | _ => false

/-! ## 3. The §9.2 entry points: the same schedule seen through `Exec/Native` -/

/-- The §9.2 pipeline on the NativeE2E fixture, pinned the same way. `prepare` is
    `parseTrace` + `verifyAlgebraicConstraints`, so this is the third place the four
    KZG squeezes are observable, and it is the one
    `verifyNative`/`prepareMsgs` actually compose. -/
def natRun (π : Bytes) : Option Obs :=
  match (prepare (Gₜ := Exp 17) n2Env Features.solidity n2Vk [[1]] [[n2Inst.toList]]).run
      (Transcript.initFromBytes π) with
  | .ok (d, t) => some (csObs d t)
  | .error _ => none

/-- The §9.2 read schedule: advice, two quotient limbs, the committed instance
    evaluation, the advice evaluation, `f_com`, `q_evals_on_x3`, `pi` = 336 bytes. -/
def natReadSchedule_ok : Bool :=
  match natRun (n2Proof n2Pi) with
  | some o => o.log == [48, 48, 48, 32, 32, 48, 32, 48] && o.pos == 336
  | none => false

/-- The x4 digest at the §9.2 shape, i.e. with the extra committed-instance read in
    front of it. -/
def natDigest_ok : Bool :=
  (natRun (n2Proof n2Pi)).map (fun o => o.digest)
    == some 112832448765355686580347398452370824893378707560978297228902381222769599072598

/-- The §9.2 guard: x3 = 13, v = 8, and the channel `verifyNative` accepts. -/
def natDual_ok : Bool :=
  match natRun (n2Proof n2Pi) with
  | some o =>
      o.lsc == [1] && o.lbas == [8] &&
      o.rsc == [1, 5, 0, 0, 6, 13, 13, 8] &&
      o.rbas == [3, 0, 1, 2, 7, 6, 8, 16] &&
      o.rlab == ["advice_0", "instance_0", "-", "-", "fixed_0", "-", "π", "-G"] &&
      o.check == true
  | none => false

/-- `prepareMsgs` re-serialises the decoded messages and runs the SAME pipeline, so
    it must reproduce the guard byte for byte, and `verifyNative` must accept it.
    This is the D6-relevant half of `verifyNative_iff_msgs`: if the refactor changed
    the schedule, the two routes would diverge here. -/
def natMsgsAgree_ok : Bool :=
  match decodeRust (Gₜ := Exp 17) n2Env Features.solidity n2Vk n2Inst (n2Proof n2Pi),
        natRun (n2Proof n2Pi) with
  | some ms, some o =>
      match prepareMsgs (Gₜ := Exp 17) n2Env keccak256 Features.solidity n2Vk n2Inst ms with
      | .ok d => (csObs d (Transcript.initFromBytes Bytes.empty)).rsc == o.rsc &&
                 match verifyMsgs (Gₜ := Exp 17) n2Env keccak256 Features.solidity expPrm
                     n2Vk n2Inst ms with
                 | .ok () => true
                 | .error _ => false
      | .error _ => false
  | _, _ => false

/-! ## 4. The phase records: the challenges, NAMED (stage 5)

    After the split, `phaseA`/`phaseB`/`phaseC` return records, so x1, x2, x3raw, x3,
    x4, fEval and v are reachable from outside the do-block for the first time. These
    gates pin them by name - which is what P-SE stage 3 needs for `Inv`, `Snapshot` and
    the x-not-in-root side condition - and they also pin the composition: the guard the
    three phases produce must be the guard `multiPrepare` produces, component for
    component. -/

/-- The three phases run in sequence on the section-1 fixture. -/
def phRun : Option (MultiPrepare.PhaseA (Fr 17) (Exp 17)
    × MultiPrepare.PhaseB (Fr 17) (Exp 17)
    × MultiPrepare.PhaseC (Fr 17) (Exp 17) (Exp 17) (Exp 17)
    × Transcript) :=
  match (phaseA (G₂ := Exp 17) (Gₜ := Exp 17) expG1Codec fc17 Features.solidity false
        mpQueries).run (Transcript.initFromBytes (csBytes (mpSlots mpPi))) with
  | .error _ => none
  | .ok (a, t1) =>
      match (phaseB expG1Codec fc17 Features.solidity a).run t1 with
      | .error _ => none
      | .ok (b, t2) =>
          match ((phaseC (G₂ := Exp 17) (Gₜ := Exp 17) expG1Codec fc17 Features.solidity a b).run t2) with
          | .error _ => none
          | .ok (c, t3) => some (a, b, c, t3)

/-- THE FOUR CHALLENGES, BY NAME. x1 = 14, x2 = 7, x3 = 10, x4 = 6, and the two values
    the contract writes to memory at the pcs checkpoint: fEval = 4 and v = 12. Before
    the split none of these had a name outside the do-block. -/
def phChallenges_ok : Bool :=
  match phRun with
  | some (a, b, c, _) =>
      ZMod.val a.x1 == 14 && ZMod.val a.x2 == 7 &&
      ZMod.val b.x3 == 10 && ZMod.val c.x4 == 6 &&
      ZMod.val b.fEval == 4 && ZMod.val c.v == 12 &&
      b.qEvalsOnX3.map ZMod.val == [7, 8] && expOf b.fCom == 6 && expOf c.pi == mpPi
  | none => false

/-- The point-set permutation is part of phaseA's output: two sets, and buildQ has
    reordered them to ascending cardinality ([[11]] alone, then [[3, 5]]). -/
def phPointSets_ok : Bool :=
  match phRun with
  | some (a, _, _, _) =>
      a.qComs.size == 2 &&
      a.pointSets.toList.map (fun (v : Array (Fr 17)) => v.toList.map ZMod.val)
        == [[11], [3, 5]]
  | none => false

/-- THE COMPOSITION IS THE FUNCTION. `phaseC.dual` must be the guard `multiPrepare`
    produces, channel by channel, and the transcript must be identical too. This is the
    executable form of the claim the D6 brief says needs no theorem: the old function IS
    the composition. It is NOT definitionally equal to the pre-split flat do-block in
    the `rfl` sense - the extra StateT.bind at each phase boundary can only be collapsed
    by case-analysing the intermediate Except - so this gate, not a proof, is the tie. -/
def phComposition_ok : Bool :=
  match phRun, mpRun mpPi with
  | some (a, b, c, t), some o =>
      c.dual.right.scalars.toList.map ZMod.val == o.rsc &&
      c.dual.right.bases.toList.map expOf == o.rbas &&
      c.dual.left.scalars.toList.map ZMod.val == o.lsc &&
      c.dual.left.bases.toList.map expOf == o.lbas &&
      c.dual.right.labels.toList.map CommitmentLabel.text == o.rlab &&
      t.pos == o.pos && t.log.toList.map Prod.fst == o.log &&
      bytesToNatBE (t.state.extract 0 32) == o.digest
  | _, _ => false

/-- The truncation, now nameable: at Fr 1009 the raw x3 is 744 and the truncated one is
    232, and BOTH are in phaseB's record, so a snapshot can state that the branch ran.
    Before the split only the truncated value existed anywhere, and only inside the
    block. -/
def phTruncNamed_ok : Bool :=
  match (phaseA (G₂ := Exp 1009) (Gₜ := Exp 1009) expG1Codec fc1009
        Features.solidity false mp9Queries).run
        (Transcript.initFromBytes (csBytes [(48, 7), (32, 0), (32, 800), (48, 1)])) with
  | .error _ => false
  | .ok (a, t1) =>
      match (phaseB expG1Codec fc1009 Features.solidity a).run t1 with
      | .ok (b, _) => ZMod.val b.x3raw == 744 && ZMod.val b.x3 == 232
      | .error _ => false


end Midfall.Instances.ChallengeStream

#eval Midfall.Instances.ChallengeStream.mpReadSchedule_ok    -- expect true
#eval Midfall.Instances.ChallengeStream.mpDigest_ok          -- expect true
#eval Midfall.Instances.ChallengeStream.mpRightChannel_ok    -- expect true
#eval Midfall.Instances.ChallengeStream.mpLeftChannel_ok     -- expect true
#eval Midfall.Instances.ChallengeStream.mpAccept_ok          -- expect true
#eval Midfall.Instances.ChallengeStream.mpNonVacuous_ok      -- expect true
#eval Midfall.Instances.ChallengeStream.mpTruncX3_ok       -- expect true
#eval Midfall.Instances.ChallengeStream.mpTruncBites_ok    -- expect true
#eval Midfall.Instances.ChallengeStream.mpTruncChangesGuard_ok  -- expect true
#eval Midfall.Instances.ChallengeStream.algReadSchedule_ok   -- expect true
#eval Midfall.Instances.ChallengeStream.algDigest_ok         -- expect true
#eval Midfall.Instances.ChallengeStream.algDual_ok           -- expect true
#eval Midfall.Instances.ChallengeStream.algAccept_ok         -- expect true
#eval Midfall.Instances.ChallengeStream.algRotWindow_ok      -- expect true
#eval Midfall.Instances.ChallengeStream.algDigestScheduleOnly_ok  -- expect true
#eval Midfall.Instances.ChallengeStream.algWindowMoved_ok    -- expect true
#eval Midfall.Instances.ChallengeStream.algR8Collapsed_ok     -- expect true
#eval Midfall.Instances.ChallengeStream.algR8NotCollapsed_ok   -- expect true
#eval Midfall.Instances.ChallengeStream.natReadSchedule_ok   -- expect true
#eval Midfall.Instances.ChallengeStream.natDigest_ok         -- expect true
#eval Midfall.Instances.ChallengeStream.natDual_ok           -- expect true
#eval Midfall.Instances.ChallengeStream.natMsgsAgree_ok      -- expect true
#eval Midfall.Instances.ChallengeStream.phChallenges_ok       -- expect true
#eval Midfall.Instances.ChallengeStream.phPointSets_ok        -- expect true
#eval Midfall.Instances.ChallengeStream.phComposition_ok      -- expect true
#eval Midfall.Instances.ChallengeStream.phTruncNamed_ok       -- expect true

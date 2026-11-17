/-
  RunLib - RUN THE LEAN VERIFIER ON THE RUST-GENERATED POSEIDON PROOF, stage by stage, at the
  real-curve model of RefModel.lean, and compare with trace.json.

  Everything Exec-side is the TREE's function, called unmodified:
     Verifier.parseTrace, Verifier.readAlgebra, Verifier.linearize,
     phaseA (unpatched, to MEASURE E-1), MultiPrepare.buildQ, phaseB, phaseC, DualMSM.split, MSMKZG.eval.
  Two shims stand in for the two proposed Exec repairs, because the tree cannot be edited:
     (S1) rotation repair   -> the imported constraint system's query lists are canonicalised
                               (value 0 / 1 / -1  ->  cur / next / prev);
     (S2) grouping repair   -> the tree's own generic `constructIntermediateSets` is instantiated at
                               C := CommitSlot x G₁z with slot equality, slots assigned in the
                               order `collectQueries` emits the queries.
-/
import RefModel
import Midfall.Instances.PoseidonEnv
import Midfall.Conformance.Bundle
import Midfall.Halo2.Exec.Native

set_option autoImplicit false

namespace RefRun
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv Midfall.Conformance

def fixtureDir : String :=
  "fixtures/conformance/poseidon"

/-! ## The data -/

/-- (S1) canonical spelling of a rotation. Under the proposed semantic `BEq Rotation` this map
    is the identity up to `==`. -/
def canonRot (r : Rotation) : Rotation :=
  if r.int == 0 then .cur else if r.int == 1 then .next else if r.int == -1 then .prev else r

def canonQ (qs : Array (Column × Rotation)) : Array (Column × Rotation) :=
  qs.map fun q => (q.1, canonRot q.2)

def csCanon : ConstraintSystem (Fr blsR) :=
  { poseidonCs with
    adviceQueries := canonQ poseidonCs.adviceQueries
    instanceQueries := canonQ poseidonCs.instanceQueries
    fixedQueries := canonQ poseidonCs.fixedQueries }

/-- Fr::DELTA of the BLS12-381 scalar field = 7^(2^32) (curves/src/bls12_381/fq.rs). -/
def deltaReal : Fr blsR := (7 : Fr blsR) ^ (2 ^ 32)

def decodeAll (hs : Array Bytes) : Option (Array G₁z) := hs.mapM g1CodecC.ofCompressed?

/-- THE REAL VERIFYING KEY: the 19 fixed and 8 sigma commitments of vk.json AS CARRIER ELEMENTS. -/
def mkVk (cs : ConstraintSystem (Fr blsR)) : Option (VerifyingKey (Fr blsR) G₁z) := do
  let fx ← decodeAll poseidonVkData.fixedCommitmentHex
  let pm ← decodeAll poseidonVkData.permutationCommitmentHex
  pure { domain := poseidonDomain, fixedCommitments := fx, permutation := { commitments := pm },
         cs := cs, csDegree := poseidonVkData.csDegree, transcriptRepr := poseidonTranscriptRepr }

/-! ## (S2) the repaired grouping, on the tree's generic function -/

inductive CommitSlot where
  | advice (proof col : Nat) | instance_ (proof col : Nat) | permProduct (proof set : Nat)
  | lookupM (proof lookup : Nat) | lookupHelper (proof lookup j : Nat) | lookupAcc (proof lookup : Nat)
  | trash (proof idx : Nat) | fixed (col : Nat) | sigma (i : Nat) | lin
  deriving BEq, Repr

abbrev Tg := CommitSlot × G₁z

/-- The slots, in the order `Verifier.collectQueries` (Exec/Verifier.lean:741-802) emits the
    queries, for ONE proof. -/
def slotsFor (vk : VerifyingKey (Fr blsR) G₁z) (nbCommitted : Nat)
    (alg : Verifier.AlgebraRead (Fr blsR) G₁z) : Array CommitSlot :=
  let adv := vk.cs.adviceQueries.toList.map fun q => CommitSlot.advice 0 q.1.index
  let inst := vk.cs.instanceQueries.toList.filterMap fun q =>
    if q.1.index < nbCommitted then some (CommitSlot.instance_ 0 q.1.index) else none
  let nsets := (alg.permutationsEvaluated[0]?.map (fun e => e.sets.size)).getD 0
  let permHead := (List.range nsets).flatMap fun i =>
    [CommitSlot.permProduct 0 i, CommitSlot.permProduct 0 i]
  let permTail := ((List.range nsets).reverse.drop 1).map fun i => CommitSlot.permProduct 0 i
  let lks := (alg.lookupsEvaluated[0]?.getD #[]).toList
  let lookup := (List.zip (List.range lks.length) lks).flatMap fun (l, ev) =>
    let nh := min ev.committed.helperPolys.size ev.evaluated.helperEvals.size
    [CommitSlot.lookupM 0 l] ++ (List.range nh).map (fun j => CommitSlot.lookupHelper 0 l j) ++
      [CommitSlot.lookupAcc 0 l, CommitSlot.lookupAcc 0 l]
  let trs := (alg.trashcansEvaluated[0]?.getD #[]).toList
  let trash := (List.range trs.length).map fun i => CommitSlot.trash 0 i
  let fixed := vk.cs.fixedQueries.toList.filterMap fun q =>
    if vk.cs.hasSimpleSelectorCol q.1.index then none else some (CommitSlot.fixed q.1.index)
  let nsig := min vk.permutation.commitments.size alg.permutationsCommon.permutationEvals.size
  let sig := (List.range nsig).map fun i => CommitSlot.sigma i
  (adv ++ inst ++ permHead ++ permTail ++ lookup ++ trash ++ fixed ++ sig ++ [CommitSlot.lin]).toArray

def tagRef (s : CommitSlot) : CommitmentReference (Fr blsR) G₁z → CommitmentReference (Fr blsR) Tg
  | .onePiece c => .onePiece (s, c)
  | .linear pts sc lb => .linear (pts.map fun c => (CommitSlot.lin, c)) sc lb

def untagRef : CommitmentReference (Fr blsR) Tg → CommitmentReference (Fr blsR) G₁z
  | .onePiece c => .onePiece c.2
  | .linear pts sc lb => .linear (pts.map fun c => c.2) sc lb

/-- THE REPAIRED RELATION (query.rs:117-133): slot equality on one-piece references, value
    equality on linear ones, labels ignored. -/
def slotBeq : CommitmentReference (Fr blsR) Tg → CommitmentReference (Fr blsR) Tg → Bool
  | .onePiece a, .onePiece b => a.1 == b.1
  | .linear p1 s1 _, .linear p2 s2 _ =>
      p1.size == p2.size && s1.size == s2.size &&
      (List.zip p1.toList p2.toList).all (fun (x, y) => decide (x.2 = y.2)) &&
      (List.zip s1.toList s2.toList).all (fun (x, y) => x == y)
  | _, _ => false

/-- A slot must agree with the label the reference attached, where the reference attached one. -/
def slotMatchesLabel : CommitSlot → CommitmentLabel → Bool
  | .advice _ c, .advice i => c == i
  | .instance_ _ c, .instance_ i => c == i
  | .fixed c, .fixed i => c == i
  | .sigma c, .permutation i => c == i
  | .permProduct .., .noLabel | .lookupM .., .noLabel | .lookupHelper .., .noLabel
  | .lookupAcc .., .noLabel | .trash .., .noLabel => true
  | .lin, .custom s => s == "linearization_poly"
  | _, _ => false

/-- phaseA (Exec/Kzg/MultiOpen.lean:235-263) with the repaired grouping. The deployed profile has
    `outerFewerPointSets = false`, so the dummy branch is not taken. -/
def phaseAR (fc : FieldConsts (Fr blsR)) (feat : Features)
    (slots : Array CommitSlot) (queries : Array (VerifierQuery (Fr blsR) G₁z)) :
    TranscriptM (MultiPrepare.PhaseA (Fr blsR) G₁z) := do
  let x1 ← tmSqueezeChallenge
  let x2 ← tmSqueezeChallenge
  let tagged : Array (VerifierQuery (Fr blsR) Tg) :=
    (List.zip slots.toList queries.toList).toArray.map fun (s, q) =>
      { point := q.point, commitmentLabel := q.commitmentLabel,
        commitment := tagRef s q.commitment, eval := q.eval }
  let (cmapT, pointSets) ← StateT.lift (constructIntermediateSets (F := Fr blsR) (C := Tg) slotBeq tagged)
  let cmap : Array (CD (Fr blsR) G₁z) := cmapT.map fun cd =>
    { commitmentLabel := cd.commitmentLabel, commitment := untagRef cd.commitment,
      setIndex := cd.setIndex, pointIndices := cd.pointIndices, evals := cd.evals }
  let (qComs, qEvalSets, pointSets) ← StateT.lift
    (MultiPrepare.buildQ (G₂ := G2fold) (Gₜ := G₁z) feat fc x1 cmap pointSets)
  pure { x1 := x1, x2 := x2, qComs := qComs, qEvalSets := qEvalSets, pointSets := pointSets }

/-! ## Printing and comparison helpers -/

def hexOf (b : Bytes) : String :=
  String.join (b.data.toList.map fun u =>
    let n := u.toNat
    let d (k : Nat) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (n / 16), d (n % 16)])

def frHex (x : Fr blsR) : String := hexOf (natToBytesBE x.val 32)
def g1Hex (Q : G₁z) : String := hexOf (g1CodecC.toCompressed Q)

def faultStr : Fault → String
  | .panic s => "PANIC " ++ s
  | .error .opening => "Error.opening"
  | .error .invalidInstances => "Error.invalidInstances"
  | .error (.transcript .unexpectedEof) => "Error.transcript(UnexpectedEof)"
  | .error (.transcript .notFound) => "Error.transcript(NotFound)"
  | .error (.transcript .other) => "Error.transcript(Other)"
  | .error _ => "Error.<other>"

def squeezes (tr : Trace) : List (String × String) :=
  tr.events.toList.filterMap fun
    | .squeeze name _ ch _ => some (name, hexOf ch)
    | _ => none

def reads (tr : Trace) : List Bytes :=
  tr.events.toList.filterMap fun
    | .read _ wire _ => some wire
    | _ => none

def cmp (what : String) (lean rust : String) : IO Bool := do
  if lean == rust then
    IO.println s!"  ok   {what}"
    pure true
  else
    IO.println s!"  DIFF {what}\n       lean {lean}\n       rust {rust}"
    pure false

def stamp (t0 : Nat) (msg : String) : IO Unit := do
  let t ← IO.monoMsNow
  IO.println s!"[{t - t0} ms] {msg}"

/-- Flip the low bit of one byte of the proof. -/
def flipByte (k : Nat) (b : Bytes) : Bytes :=
  ByteArray.mk ((List.zip (List.range b.size) b.data.toList).map fun (i, u) =>
    if i == k then Nat.toUInt8 (Nat.xor u.toNat 1) else u).toArray

/-- Indices of the identity elements of an array of carrier elements. -/
def identityCols (cs : Array G₁z) : List Nat :=
  (List.zip (List.range cs.size) cs.toList).filterMap fun (i, c) => if c = 1 then some i else none

/-! ## The run -/

def loadBundle : IO (Bytes × Trace × Array (Array Bytes) × Array (Array Bytes)) := do
  let proof ← IO.FS.readBinFile (fixtureDir ++ "/proof.bin")
  let traceTxt ← IO.FS.readFile (fixtureDir ++ "/trace.json")
  let instTxt ← IO.FS.readFile (fixtureDir ++ "/instances.json")
  let tr ← IO.ofExcept ((jParse traceTxt >>= Midfall.Conformance.parseTrace).mapError IO.userError)
  let (c, pb) ← IO.ofExcept ((jParse instTxt >>= parseInstances).mapError IO.userError)
  pure (proof, tr, c, pb)

/-- The whole pipeline. `cs` chooses the constraint system (raw import or canonicalised),
    `repaired` chooses the grouping. Returns `true` iff every compared value agreed. -/
def run (label : String) (cs : ConstraintSystem (Fr blsR)) (repaired : Bool) (evalMsm : Bool)
    (delta : Fr blsR := deltaReal) (mutate : Bytes → Bytes := id)
    (trapdoor : Option (ZMod blsR) := none) : IO Bool := do
  let t0 ← IO.monoMsNow
  IO.println s!"=== {label} ==="
  let (proof0, tr, committedHex, publicHex) ← loadBundle
  let proof := mutate proof0
  let some vk := mkVk cs | do IO.println "VK: a commitment did not decode"; return false
  stamp t0 s!"VK built: {vk.fixedCommitments.size} fixed + {vk.permutation.commitments.size} sigma commitments decoded into G₁z; identity fixed columns = {identityCols vk.fixedCommitments}"
  -- instances.json: one committed column (the identity), one public column with one value
  let some committed := (committedHex.mapM fun row => row.mapM g1CodecC.ofCompressed?)
    | do IO.println "instances.json: committed point did not decode"; return false
  -- one proof; its public columns; each column the list of its values (one value for poseidon)
  let instances : Array (Array (Array (Fr blsR))) :=
    publicHex.map fun row => row.map fun b => #[((bytesToNatBE b : Nat) : Fr blsR)]
  let feat := Features.solidity
  let tr0 := Transcript.initFromBytes proof
  -- STAGE 1: parse_trace
  let (vt, t1) ← match (Midfall.Halo2.parseTrace g1CodecC feat vk committed instances).run tr0 with
    | .ok r => pure r
    | .error f => do IO.println s!"STAGE 1 parseTrace FAILED: {faultStr f}"; return false
  stamp t0 s!"stage 1 parseTrace ok: pos={t1.pos}, reads={t1.log.size}"
  let sq := squeezes tr
  let want (n : String) : String := ((sq.find? fun e => e.1 == n).map fun e => e.2).getD "<absent>"
  let mut ok := true
  ok := (← cmp "theta" (frHex vt.theta) (want "theta")) && ok
  ok := (← cmp "beta" (frHex vt.beta) (want "beta")) && ok
  ok := (← cmp "gamma" (frHex vt.gamma) (want "gamma")) && ok
  ok := (← cmp "trash_challenge" (frHex vt.trashChallenge) (want "trash_challenge")) && ok
  ok := (← cmp "y" (frHex vt.y) (want "y")) && ok
  -- STAGE 2: read_algebra
  let nbCommitted := (committed[0]?.map (fun r => r.size)).getD 0
  let (alg, t2) ← match (Verifier.readAlgebra g1CodecC feat vk vt.permutations vt.lookups
      vt.trashcans nbCommitted instances.size instances).run t1 with
    | .ok r => pure r
    | .error f => do IO.println s!"STAGE 2 readAlgebra FAILED: {faultStr f}"; return false
  stamp t0 s!"stage 2 readAlgebra ok: pos={t2.pos}, reads={t2.log.size}"
  ok := (← cmp "x" (frHex alg.x) (want "x")) && ok
  -- STAGE 3: linearize (identities, linearization commitment, queries)
  let queries ← match Verifier.linearize delta vk vt.adviceCommitments committed vt.y vt.beta
      vt.gamma vt.theta vt.trashChallenge vt.challenges alg with
    | .ok q => pure q
    | .error f => do IO.println s!"STAGE 3 linearize FAILED: {faultStr f}"; return false
  stamp t0 s!"stage 3 linearize ok: {queries.size} queries"
  -- STAGE 4: multi_prepare
  let (a, t3) ←
    if repaired then do
      let slots := slotsFor vk nbCommitted alg
      let labelsOk := slots.size == queries.size &&
        (List.zip slots.toList queries.toList).all fun (s, q) => slotMatchesLabel s q.commitmentLabel
      IO.println s!"  slots: {slots.size} for {queries.size} queries; every slot agrees with its label: {labelsOk}"
      unless labelsOk do return false
      match (phaseAR poseidonFc feat slots queries).run t2 with
      | .ok r => pure r
      | .error f => do IO.println s!"STAGE 4 phaseA (REPAIRED grouping) FAILED: {faultStr f}"; return false
    else
      match (phaseA (G₂ := G2fold) (Gₜ := G₁z) g1CodecC poseidonFc feat false queries).run t2 with
      | .ok r => pure r
      | .error f => do IO.println s!"STAGE 4 phaseA (TREE grouping, kzgCommitBeq) FAILED: {faultStr f}"; return false
  stamp t0 s!"stage 4a phaseA ok: {a.pointSets.size} point sets of sizes {a.pointSets.toList.map (·.size)}, {a.qComs.size} q_coms"
  ok := (← cmp "x1" (frHex a.x1) (want "x1")) && ok
  ok := (← cmp "x2" (frHex a.x2) (want "x2")) && ok
  let (b, t4) ← match (phaseB g1CodecC poseidonFc feat a).run t3 with
    | .ok r => pure r
    | .error f => do IO.println s!"STAGE 4 phaseB FAILED: {faultStr f}"; return false
  ok := (← cmp "x3 (truncated)" (frHex b.x3) (want "x3")) && ok
  let (c, t5) ← match (phaseC (G₂ := G2fold) (Gₜ := G₁z) g1CodecC poseidonFc feat a b).run t4 with
    | .ok r => pure r
    | .error f => do IO.println s!"STAGE 4 phaseC FAILED: {faultStr f}"; return false
  ok := (← cmp "x4" (frHex c.x4) (want "x4")) && ok
  stamp t0 s!"stage 4 multiPrepare ok: pos={t5.pos}/{proof.size}, reads={t5.log.size}"
  -- the read schedule, byte for byte
  let leanReads := t5.log.toList.map fun r => hexOf r.2
  let rustReads := (reads tr).map hexOf
  ok := (← cmp s!"read schedule ({leanReads.length} reads, widths and bytes)" (toString leanReads.length ++ ":" ++ toString (hash leanReads))
      (toString rustReads.length ++ ":" ++ toString (hash rustReads))) && ok
  ok := (← cmp "assert_empty" (toString (t5.buffer.size == t5.pos)) "true") && ok
  -- STAGE 5: the final MSM, term by term
  let (lt, rt) := c.dual.split
  let showT (t : CommitmentLabel × Fr blsR × G₁z) : String := t.1.text ++ "|" ++ frHex t.2.1 ++ "|" ++ g1Hex t.2.2
  let showR (t : Term) : String := t.label ++ "|" ++ hexOf t.scalar ++ "|" ++ hexOf t.point
  ok := (← cmp s!"dual_msm.left  ({lt.size} terms)" (toString (lt.toList.map showT)) (toString (tr.leftTerms.toList.map showR))) && ok
  let lr := rt.toList.map showT
  let rr := tr.rightTerms.toList.map showR
  if lr == rr then IO.println s!"  ok   dual_msm.right ({rt.size} terms: label, scalar, point)"
  else
    ok := false
    IO.println s!"  DIFF dual_msm.right: lean {lr.length} terms, rust {rr.length} terms"
    for (i, (x, y)) in (List.zip (List.range lr.length) (List.zip lr rr)) do
      if x != y then IO.println s!"       [{i}] lean {x}\n       [{i}] rust {y}"
  stamp t0 "stage 5 final MSM terms compared"
  if evalMsm then
    ok := (← cmp "left.eval  (pairing_lhs)" (g1Hex c.dual.left.eval) (hexOf tr.leftEval)) && ok
    ok := (← cmp "right.eval (pairing_rhs)" (g1Hex c.dual.right.eval) (hexOf tr.rightEval)) && ok
    stamp t0 "stage 6 MSM evaluated"
  -- the final check of DualMSM.check at the constructed pairing: e(left, sG2) + e(right, -G2) = 0,
  -- i.e. s • left - right = 0 in G₁z. Decidable in the VM once the trapdoor is DATA.
  match trapdoor with
  | none => pure ()
  | some s =>
      let params : ParamsVerifierKZG G₁z G2fold :=
        ParamsVerifierKZG.ofParams (g2foldExp 1) (Multiplicative.ofAdd s)
      let verdict := DualMSM.check c.dual params
      stamp t0 s!"DualMSM.check at trapdoor {s.val} (tree function, constructed pairing): {verdict}"
  IO.println s!"=== {label}: {if ok then "ALL COMPARED VALUES AGREE" else "MISMATCH"} (rust verdict in trace.json: {tr.verdict}, pairing_check={tr.pairingCheck}) ==="
  pure ok

end RefRun

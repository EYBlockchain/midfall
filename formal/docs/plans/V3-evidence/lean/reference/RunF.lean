import RunLib
set_option autoImplicit false
/-! Is the CommitmentLabel a sufficient grouping key? Measured on the real query vector. -/
namespace RefRun
open Midfall Midfall.Yul Midfall.Instances Midfall.Assumptions Midfall.Halo2 RefModel
open Midfall.Instances.PoseidonFixture Midfall.Instances.PoseidonEnv Midfall.Conformance

def labelKind : CommitmentLabel → String
  | .advice _ => "advice" | .instance_ _ => "instance" | .fixed _ => "fixed"
  | .permutation _ => "vk_perm" | .custom _ => "custom" | .noLabel => "noLabel"

/-- Grouping keyed on the query LABEL (the cheaper repair one might reach for). -/
def labelBeq : CommitmentReference (Fr blsR) (CommitmentLabel × G₁z) →
    CommitmentReference (Fr blsR) (CommitmentLabel × G₁z) → Bool
  | .onePiece a, .onePiece b => a.1 == b.1
  | .linear .., .linear .. => true
  | _, _ => false

def labelStudy : IO Unit := do
  let (proof, _, committedHex, publicHex) ← loadBundle
  let some vk := mkVk csCanon | IO.println "vk"
  let some committed := (committedHex.mapM fun row => row.mapM g1CodecC.ofCompressed?) | IO.println "ci"
  let instances : Array (Array (Array (Fr blsR))) :=
    publicHex.map fun row => row.map fun b => #[((bytesToNatBE b : Nat) : Fr blsR)]
  let feat := Features.solidity
  let .ok (vt, t1) := (Midfall.Halo2.parseTrace g1CodecC feat vk committed instances).run
      (Transcript.initFromBytes proof) | IO.println "s1"
  let .ok (alg, _) := (Verifier.readAlgebra g1CodecC feat vk vt.permutations vt.lookups
      vt.trashcans 1 instances.size instances).run t1 | IO.println "s2"
  let .ok queries := Verifier.linearize deltaReal vk vt.adviceCommitments committed vt.y vt.beta
      vt.gamma vt.theta vt.trashChallenge vt.challenges alg | IO.println "s3"
  let slots := slotsFor vk 1 alg
  let kinds := ["advice", "instance", "noLabel", "fixed", "vk_perm", "custom"]
  for k in kinds do
    let idx := (List.range queries.size).filter fun i =>
      (queries[i]?.map fun q => labelKind q.commitmentLabel == k) == some true
    let ss := idx.filterMap fun i => slots[i]?
    let distinct := ss.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) ([] : List CommitSlot)
    IO.println s!"  label kind {k}: {idx.length} queries, {distinct.length} distinct allocations"
  -- queries opened at x itself whose commitment VALUE is the identity
  let idAtX := (List.range queries.size).filter fun i =>
    match queries[i]? with
    | some q => (match q.commitment with | .onePiece c => decide (c = 1) | _ => false) && q.point == alg.x
    | none => false
  IO.println s!"  one-piece queries at x whose commitment is the identity: {idAtX.length} (labels {idAtX.filterMap fun i => queries[i]?.map fun q => q.commitmentLabel.text})"
  -- label-keyed grouping on the real vector
  let tagged : Array (VerifierQuery (Fr blsR) (CommitmentLabel × G₁z)) := queries.map fun q =>
    { point := q.point, commitmentLabel := q.commitmentLabel, eval := q.eval,
      commitment := match q.commitment with
        | .onePiece c => .onePiece (q.commitmentLabel, c)
        | .linear pts sc lb => .linear (pts.map fun c => (CommitmentLabel.noLabel, c)) sc lb }
  match constructIntermediateSets (F := Fr blsR) labelBeq tagged with
  | .ok (cm, ps) => IO.println s!"  LABEL-keyed grouping: ok, {cm.size} commitments, {ps.size} point sets"
  | .error f => IO.println s!"  LABEL-keyed grouping: {faultStr f}"
  -- slot-keyed grouping on the real vector
  let taggedS : Array (VerifierQuery (Fr blsR) Tg) :=
    (List.zip slots.toList queries.toList).toArray.map fun (s, q) =>
      { point := q.point, commitmentLabel := q.commitmentLabel, commitment := tagRef s q.commitment, eval := q.eval }
  match constructIntermediateSets (F := Fr blsR) slotBeq taggedS with
  | .ok (cm, ps) => IO.println s!"  SLOT-keyed grouping:  ok, {cm.size} commitments, {ps.size} point sets of sizes {ps.toList.map (·.size)}"
  | .error f => IO.println s!"  SLOT-keyed grouping:  {faultStr f}"
  -- value-keyed grouping (the tree today)
  match constructIntermediateSets (F := Fr blsR) (C := G₁z) (kzgCommitBeq (G₂ := G2fold) (Gₜ := G₁z)) queries with
  | .ok (cm, ps) => IO.println s!"  VALUE-keyed grouping (tree): ok, {cm.size} commitments, {ps.size} point sets"
  | .error f => IO.println s!"  VALUE-keyed grouping (tree): {faultStr f}"

end RefRun
#eval RefRun.labelStudy

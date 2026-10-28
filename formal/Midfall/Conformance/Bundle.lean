-- |
-- Midfall.Conformance.Bundle
--
-- Typed loading of the exporter bundle (docs/conformance-schema.md) through
-- `Midfall.Common.Json`. Every field is read with a strict accessor: a missing key,
-- a float where a nat is required, a hex string of the wrong width or the wrong
-- case all fail rather than defaulting, which is the whole reason
-- `Common/Json.lean` refuses to truncate.
--
-- FINDING (hazard 2). `Common/Json.lean` addresses fields by key only - `jNat o k`,
-- `jArray o k` - and has no element-level accessor, so an array of numbers or of hex
-- strings cannot be read strictly with what is there. The runner needs
-- `advice_column_phase` (array of nats), `instance_queries` (array of pairs whose
-- second component is a SIGNED rotation), `fixed_commitments_compressed_hex` (array
-- of hex strings) and `absorbed_before_hex` (array of arrays of hex strings). Rather
-- than edit another package's file, the element-level counterparts are defined here
-- under the same rules. Nothing about the exporter was bent to fit the parser: the
-- shapes are the schema's, and the parser gap is reported rather than hidden.
--
-- A second, smaller finding: `public` is a Lean keyword, so a bundle field cannot
-- carry the JSON key's name. `instances.json` keeps its schema name `public`; the
-- Lean record calls the field `publicCols`. Recorded per the standing note that
-- every reserved-word deviation must be named at the site.

import Lean
import Midfall.Common.Json
import Midfall.Common.Bytes
import Midfall.Assumptions.Pairing

namespace Midfall.Conformance

open Midfall

/-! ## Element-level strict accessors

    The array counterparts of `jNat` / `jString` / `jBool` / `jArray`, with the same
    refusal to coerce. `Json.lean`'s own comment explains why a number goes through
    its printed form: `Lean.JsonNumber`'s constructors are not matchable from outside
    Lean core, so "12.5" must be rejected by failing to parse as a nat rather than by
    truncating. -/

def jNatVal (v : JValue) : Except String Nat :=
  match v with
  | Lean.Json.num n =>
      match n.toString.toNat? with
      | some x => .ok x
      | none => .error ("json: array element is not a nat (got " ++ n.toString ++ ")")
  | _ => .error "json: array element is not a number"

/-- A rotation in Rust is an `i32`, so a negative one is legal and cannot go through
    `jNatVal`. Kept as an `Int` for exactly that reason. -/
def jIntVal (v : JValue) : Except String Int :=
  match v with
  | Lean.Json.num n =>
      match n.toString.toInt? with
      | some x => .ok x
      | none => .error ("json: array element is not an int (got " ++ n.toString ++ ")")
  | _ => .error "json: array element is not a number"

def jStrVal (v : JValue) : Except String String :=
  match v with
  | Lean.Json.str s => .ok s
  | _ => .error "json: array element is not a string"

def jBoolVal (v : JValue) : Except String Bool :=
  match v with
  | Lean.Json.bool b => .ok b
  | _ => .error "json: array element is not a bool"

def jArrVal (v : JValue) : Except String (Array JValue) :=
  match v with
  | Lean.Json.arr a => .ok a
  | _ => .error "json: value is not an array"

def jNatArr (o : JValue) (k : String) : Except String (Array Nat) := do
  let a ← jArray o k
  a.mapM jNatVal

/-- An array of hex strings of any even width (points, scalars, whatever the field
    holds). -/
def jHexArr (o : JValue) (k : String) : Except String (Array Bytes) := do
  let a ← jArray o k
  a.mapM fun v => do jHexBytes' (← jStrVal v)

/-- An array of `[column_index, rotation]` pairs, exactly as the schema writes
    `instance_queries`. -/
def jQueryArr (o : JValue) (k : String) : Except String (Array (Nat × Int)) := do
  let a ← jArray o k
  a.mapM fun pair => do
    let xs ← jArrVal pair
    if xs.size ≠ 2 then
      .error ("json: " ++ k ++ " entry is not a [col, rotation] pair")
    else
      let col ← jNatVal xs[0]!
      let rot ← jIntVal xs[1]!
      .ok (col, rot)

/-- A two-level array: `instances.json` groups columns by proof row. -/
def jHexRows (o : JValue) (k : String) : Except String (Array (Array Bytes)) := do
  let rows ← jArray o k
  rows.mapM fun row => do
    let xs ← jArrVal row
    xs.mapM fun x => do jHexBytes' (← jStrVal x)

/-! ## The bundle -/

/-- The `vk.json` fields the replay consumes. -/
structure VkInfo where
  schema : Nat
  k : Nat
  n : Nat
  csDegree : Nat
  quotientPolyDegree : Nat
  /-- 32 bytes, big-endian: the imported scalar of D-P1/R-1. The runner ASSERTS
      this against the transcript rather than trusting it. -/
  transcriptRepr : Bytes
  numAdviceColumns : Nat
  numFixedColumns : Nat
  numInstanceColumns : Nat
  numChallenges : Nat
  nbPublicInputs : Nat
  numCommittedInstances : Nat
  /-- The deployed profile (D-P14/R-22): x3 is truncated after sampling, so the
      recorded challenge is NOT `digest mod r` for that one squeeze. -/
  truncatedChallenges : Bool
  /-- `Fq::NUM_BITS`, the width `truncate` works from. -/
  scalarNumBits : Nat

inductive Ev where
  | absorb (tag : String) (bytes : Bytes)
  | read (name : String) (wire : Bytes) (absorbed : Bytes)
  | squeeze (name : String) (digest : Bytes) (challenge : Bytes) (before : Array Bytes)
  deriving BEq

/-- One `(scalar, point, label)` MSM term from `dual_msm`. -/
structure Term where
  label : String
  scalar : Bytes
  point : Bytes
  deriving BEq

structure Trace where
  verdict : String
  error : String
  pairingCheck : Bool
  proofLen : Nat
  events : Array Ev
  leftTerms : Array Term
  rightTerms : Array Term
  leftEval : Bytes
  rightEval : Bytes
  /-- `fixture_match.proof`: does the regenerated proof equal the committed
      `fixtures/poseidon/proof.bin`? Decides whether the committed
      `rust_trace.json` can be compared by value or only by shape. -/
  fixtureProofMatch : Bool

structure Bundle where
  vk : VkInfo
  /-- `instances.json.committed`: per proof row, the committed instance columns as
      48-byte compressed point encodings. -/
  committed : Array (Array Bytes)
  /-- `instances.json.public`: per proof row, the public instance columns as
      32-byte big-endian scalars. Named `publicCols` because `public` is a Lean
      keyword (see the header). -/
  publicCols : Array (Array Bytes)
  proof : Bytes
  trace : Trace

/-! ## Parsers -/

def parseVk (j : JValue) : Except String VkInfo := do
  let repr ← jHexBytes' (← jString j "transcript_repr_be_hex")
  pure {
    schema := (← jNat j "schema"), k := (← jNat j "k"), n := (← jNat j "n"),
    csDegree := (← jNat j "cs_degree"),
    quotientPolyDegree := (← jNat j "quotient_poly_degree"),
    transcriptRepr := repr,
    numAdviceColumns := (← jNat j "num_advice_columns"),
    numFixedColumns := (← jNat j "num_fixed_columns"),
    numInstanceColumns := (← jNat j "num_instance_columns"),
    numChallenges := (← jNat j "num_challenges"),
    nbPublicInputs := (← jNat j "nb_public_inputs"),
    numCommittedInstances := (← jNat j "num_committed_instances"),
    truncatedChallenges := (← jBool j "truncated_challenges"),
    scalarNumBits := (← jNat j "scalar_num_bits")
  }

def parseEv (v : JValue) : Except String Ev := do
  let kind ← jString v "kind"
  match kind with
  | "absorb" => do
      let tag ← jString v "tag"
      let bytes ← jHexBytes' (← jString v "bytes_be_hex")
      .ok (.absorb tag bytes)
  | "read" => do
      let name ← jString v "tag"
      let wire ← jHexBytes' (← jString v "wire_hex")
      let absorbed ← jHexBytes' (← jString v "absorbed_be_hex")
      .ok (.read name wire absorbed)
  | "squeeze" => do
      let name ← jString v "name"
      let arr ← jArray v "absorbed_before_hex"
      let before ← arr.mapM fun x => do jHexBytes' (← jStrVal x)
      let digest ← jHexBytes' (← jString v "digest_be_hex")
      let challenge ← jHexBytes' (← jString v "challenge_be_hex")
      .ok (.squeeze name digest challenge before)
  | other => .error ("trace.json: unknown event kind " ++ other)

def parseTerms (j : JValue) (k : String) : Except String (Array Term) := do
  let a ← jArray j k
  a.mapM fun t => do
    let label ← jString t "label"
    let scalar ← jHexBytes' (← jString t "scalar_be_hex")
    let point ← jHexBytes' (← jString t "point_compressed_hex")
    .ok { label := label, scalar := scalar, point := point }

/-- `error` is `null` on an accepting run, so it is not a `jString` site. Read
    leniently but only here: every other field keeps its strict accessor. -/
def jsonOrNullStr (o : JValue) (k : String) : String :=
  match o.getObjVal? k with
  | .ok (Lean.Json.str s) => s
  | .ok Lean.Json.null => ""
  | .ok _ => "<non-string>"
  | .error _ => "<absent>"

def parseTrace (j : JValue) : Except String Trace := do
  let msm ← jObject j "dual_msm"
  let fm ← jObject j "fixture_match"
  let log ← jArray j "transcript_log"
  let events ← log.mapM parseEv
  let leftTerms ← parseTerms msm "left"
  let rightTerms ← parseTerms msm "right"
  let leftEval ← jHexBytes' (← jString msm "left_eval_compressed_hex")
  let rightEval ← jHexBytes' (← jString msm "right_eval_compressed_hex")
  pure {
    verdict := (← jString j "verdict"),
    error := jsonOrNullStr j "error",
    pairingCheck := (← jBool j "pairing_check"),
    proofLen := (← jNat j "proof_len"),
    events := events, leftTerms := leftTerms, rightTerms := rightTerms,
    leftEval := leftEval, rightEval := rightEval,
    fixtureProofMatch := (← jBool fm "proof")
  }

def parseInstances (j : JValue) :
    Except String (Array (Array Bytes) × Array (Array Bytes)) := do
  let c ← jHexRows j "committed"
  let p ← jHexRows j "public"
  .ok (c, p)

end Midfall.Conformance

-- |
-- Midfall.Common.Json
--
-- Typed, TOTAL access over JSON, for the conformance harness (plan Section 5).
-- Built on Lean core's Lean.Json: the parser is not the thing under test, and a
-- bespoke one would be one more surface to validate.
--
-- Every accessor returns Except String and names the failing key. Nothing
-- silently defaults: a fixture loader that quietly substitutes a missing field is
-- how a conformance run passes while comparing nothing.

import Lean
import Midfall.Common.Bytes

namespace Midfall

/-- A JSON value, aliased so callers do not depend on Lean core's path. -/
abbrev JValue := Lean.Json

/-- Parse JSON text; Lean's parser reports a position in the error string. -/
def jParse (text : String) : Except String JValue := Lean.Json.parse text

def jString (o : JValue) (k : String) : Except String String :=
  match o.getObjVal? k with
  | .ok (Lean.Json.str s) => .ok s
  | .ok _ => .error ("json: " ++ k ++ " is not a string")
  | .error e => .error e

def jBool (o : JValue) (k : String) : Except String Bool :=
  match o.getObjVal? k with
  | .ok (Lean.Json.bool b) => .ok b
  | .ok _ => .error ("json: " ++ k ++ " is not a bool")
  | .error e => .error e

/-- The value under k, without a shape test: Lean's Json.obj carries an implicit
    ordering argument and is not matchable from here. Any later jString/jNat/jArray
    on a non-object fails with its own message, so nothing is defaulted. -/
def jObject (o : JValue) (k : String) : Except String JValue := o.getObjVal? k

def jArray (o : JValue) (k : String) : Except String (Array JValue) :=
  match o.getObjVal? k with
  | .ok (Lean.Json.arr a) => .ok a
  | .ok _ => .error ("json: " ++ k ++ " is not an array")
  | .error e => .error e

/-- A natural-number field. JsonNumber's constructors are not matchable from
    outside Lean core, so this goes through the printed form: "12" parses, while
    "12.5" and "-3" are rejected rather than truncated. -/
def jNat (o : JValue) (k : String) : Except String Nat :=
  match o.getObjVal? k with
  | .ok (Lean.Json.num n) =>
      match n.toString.toNat? with
      | some v => .ok v
      | none => .error ("json: " ++ k ++ " is not a nat (got " ++ n.toString ++ ")")
  | .ok _ => .error ("json: " ++ k ++ " is not a number")
  | .error e => .error e

/-- A lowercase hex string of exactly nBytes bytes. Strict about length, case and
    alphabet: docs/REVIEW.md R-20 is why a width slip must fail here rather than
    yield a plausible-looking wrong value. -/
def jHexBytes (s : String) (nBytes : Nat) : Except String Bytes :=
  let cs := s.toList
  if cs.length ≠ 2 * nBytes then
    .error ("hex: expected " ++ toString nBytes ++ " bytes, got "
            ++ toString (cs.length / 2) ++ " (" ++ toString cs.length
            ++ " hex chars)")
  else go cs #[]
where
  decode (c : Char) : Except String Nat :=
    let v := c.val.toNat
    if 97 <= v && v <= 102 then .ok (v - 87)
    else if 48 <= v && v <= 57 then .ok (v - 48)
    else .error ("hex: invalid character " ++ String.singleton c)
  go : List Char -> Array UInt8 -> Except String Bytes
    | [], acc => .ok (ByteArray.mk acc)
    | a :: b :: rest, acc => do
        let x <- decode a
        let y <- decode b
        go rest (acc.push (Nat.toUInt8 (x * 16 + y)))
    | [_], _ => .error "hex: odd number of digits"

/-- A hex string of ANY even length, for fields whose width varies (the trace
    stores 32-byte scalars and 48-byte points under different keys). -/
def jHexBytes' (s : String) : Except String Bytes :=
  jHexBytes s (s.length / 2)

section Kats

def jsonKats_ok : Bool :=
  match jParse "{\"n\": 12, \"s\": \"ab\", \"b\": true, \"f\": 12.5}" with
  | .error _ => false
  | .ok j =>
      (match jNat j "n" with | .ok n => n == 12 | .error _ => false) &&
      (match jString j "s" with | .ok s => s == "ab" | .error _ => false) &&
      (match jBool j "b" with | .ok b => b = true | .error _ => false) &&
      -- a float where a nat is required is refused, not truncated
      (match jNat j "f" with | .error _ => true | .ok _ => false) &&
      (match jString j "absent" with | .error _ => true | .ok _ => false) &&
      (match jBool j "n" with | .error _ => true | .ok _ => false) &&
      (match jArray j "s" with | .error _ => true | .ok _ => false)

def hexKats_ok : Bool :=
  (match jHexBytes "81e6" 2 with
   | .ok b => b.data.toList == [0x81, 0xe6] | .error _ => false) &&
  (match jHexBytes "81e6" 3 with | .error _ => true | .ok _ => false) &&
  (match jHexBytes "81e" 2 with | .error _ => true | .ok _ => false) &&
  (match jHexBytes "81zz" 2 with | .error _ => true | .ok _ => false) &&
  (match jHexBytes "81E6" 2 with | .error _ => true | .ok _ => false) &&
  (match jHexBytes "" 0 with | .ok b => b.size == 0 | .error _ => false) &&
  (match jHexBytes' "81e60c" with | .ok b => b.size == 3 | .error _ => false)

end Kats

#eval Midfall.jsonKats_ok   -- expect true
#eval Midfall.hexKats_ok    -- expect true

end Midfall

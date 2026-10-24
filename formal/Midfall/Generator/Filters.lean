-- |
-- Midfall.Generator.Filters
--
-- The Askama (Jinja-shaped) filters and Rust Display impls that decide how a
-- number becomes bytes in the rendered artifact. Ported exactly: rule R1 puts
-- one Lean def per Rust fn, and rule R10 makes all of it computable.
--
-- These are the ONLY place the hex spelling rules are defined. They matter for
-- more than the renderer: the vendored 'YulSemantics.Literal' records a literal's
-- VALUE and not its spelling, so the three formatters the Rust uses ('hex()',
-- 'hex_padded(pad)', '{:#x}') cannot be recovered from the AST - see
-- Midfall/Generator/Render.lean, loss class 2, and docs/ecosystem.md section 11.
-- Porting the filters is therefore necessary even though the renderer prints
-- decimal: the spelling has to live somewhere, and it lives here.

namespace Midfall.Generator

/-- Lowercase hex nibbles of a natural, minimal width, "0" for zero: exactly
    what Rust 'format!("{:x}", n)' produces for a usize or a U256. Lean's
    'Nat.toDigits' already emits lowercase chars and already renders 0 as ['0']. -/
def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- Left-pad a string to 'pad' characters with 'c'. Rust's '{value:0pad$x}'. -/
def padLeft (pad : Nat) (c : Char) (s : String) : String :=
  String.ofList (List.replicate (pad - s.length) c) ++ s

/-- rust: proofs/solidity-verifier/src/lowering/render/models.rs:1019-1028
    (Askama filter 'hex'). Lowercase, minimal nibbles, then ONE pad zero when
    the nibble count is odd so every literal has byte width. Note the pad is
    '0x0{hex}', never a general left-pad: 4096 renders '0x1000', not '0x01000'. -/
def hexFilter (n : Nat) : String :=
  let value := hexDigits n
  if value.length % 2 == 1 then "0x0" ++ value else "0x" ++ value

/-- rust: proofs/solidity-verifier/src/lowering/render/models.rs:1030-1038
    (Askama filter 'hex_padded'). Zero-pad to 'pad' nibbles. The 'if string ==
    "0x0"' arm is not dead code: with 'pad = 0' Rust's '{:00x}' yields "0" and
    the guard turns it into the bare prefix "0x". Ported as written rather than
    simplified. -/
def hexPaddedFilter (pad : Nat) (n : Nat) : String :=
  let string := "0x" ++ padLeft pad '0' (hexDigits n)
  if string == "0x0" then "0x" ++ String.ofList (List.replicate pad '0') else string

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:625-633
    ('fmt_hex'). The Rust takes an 'isize' and casts with 'as usize' BEFORE
    formatting, so a negative would wrap to a 16-nibble literal rather than
    print a minus sign. 'Value's Display impl never routes a negative here (it
    emits 'sub(0, ...)' first, encoding/mod.rs:640), so the wrap is unreachable
    - but it is ported, not normalised away: see docs/REVIEW.md R-32 for what
    happens when one arm of a pair gets normalised and the other does not. -/
def fmtHex (off : Int) : String :=
  hexFilter (if off < 0 then (off + (2 : Int)^64).toNat else off.toNat)

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:573-579
    ('enum Location'). -/
inductive Location where
  | calldata
  | memory

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:581-592
    ('enum Value'). A byte offset, either concrete or symbolic in an identifier.
    'isize' semantics are kept by using 'Int', so 'sub(name, 0x20)' can be
    produced by arithmetic on a small base offset rather than only by hand. -/
inductive Value where
  | integer (i : Int)
  | identifier (name : String) (off : Int)

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:635-650
    ('impl Display for Value'). Five arms, in the Rust's order. The zero-offset
    arm prints the bare identifier; a positive offset prints 'add(name, 0xNN)';
    a negative one prints 'sub(name, 0xNN)' with the ABSOLUTE offset; and a
    negative integer prints 'sub(0, 0xNN)'. -/
def printValue (v : Value) : String :=
  match v with
  | .integer i => if i >= 0 then fmtHex i else "sub(0, " ++ fmtHex (-i) ++ ")"
  | .identifier name 0 => name
  | .identifier name off =>
    if off > 0 then "add(" ++ name ++ ", " ++ fmtHex off ++ ")"
    else "sub(" ++ name ++ ", " ++ fmtHex (-off) ++ ")"

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:716-721
    ('impl Display for Ptr'): a pointer renders as its value expression, the
    location is not printed. -/
def printPtr (v : Value) : String := printValue v

/-- rust: proofs/solidity-verifier/src/lowering/encoding/mod.rs:764-775
    ('impl Display for Word'): the load expression for the location. Note the
    comment in the Rust: calldata words are read with 'calldataload' because the
    proof shim stores scalars as canonical big-endian words. -/
def printWord (loc : Location) (v : Value) : String :=
  match loc with
  | .calldata => "calldataload(" ++ printValue v ++ ")"
  | .memory => "mload(" ++ printValue v ++ ")"

end Midfall.Generator

/-! # Known-answer tests

Every expected string below is a byte sequence copied out of the committed
artifacts, not a value these functions were asked to produce. That is the point:
docs/REVIEW.md R-20 and R-34 are both about checks that stayed green because
each side of the comparison came from the same definition. -/
namespace Midfall.Generator

/-- Every value below is a hex literal that occurs in the CURRENT generated output
    (target/poseidon-fixture-dump, regenerated by commit 5312cb7). In list order the
    sites are: V:271, V:271, V:106, V:333, VK:64, V:376, V:369, V:376, V:418, V:420, V:106, V:650.
    The deployed deployments/sepolia/moonlight-wrap artifact was NOT used - it
    predates the current templates by five months. -/
def hexFilter_kats : List (Nat × String) := [
  (0, "0x00"),
  (1, "0x01"),
  (16, "0x10"),
  (32, "0x20"),
  (254, "0xfe"),
  (256, "0x0100"),
  (768, "0x0300"),
  (11, "0x0b"),
  (12, "0x0c"),
  (15, "0x0f"),
  (4096, "0x1000"),
  (10240, "0x2800"),
]

def hexFilter_kats_ok : Bool := hexFilter_kats.all fun (n, want) => hexFilter n = want

/-- hex_padded(4) and hex_padded(64) from the VK payload stores, hex_padded(2)
    from the ABI cursor constants. Note 0x1144 is FOUR nibbles although the
    filter was called with pad = 2: Rust
    '{:02x}' is a minimum width, so a wider value is not truncated. -/
def hexPadded_kats : List (Nat × Nat × String) := [
  (4, 0, "0x0000"),
  (4, 32, "0x0020"),
  (4, 64, "0x0040"),
  (64, 1, "0x0000000000000000000000000000000000000000000000000000000000000001"),
  (64, 6, "0x0000000000000000000000000000000000000000000000000000000000000006"),
  (64, 34720129961312545684992424441958071501550675660370520772129419266726773916820, "0x4cc2e5ac0d3a524691c3723a18e826d6ed01cbf767fdec83fcf3a8f9e7640494"),
  (2, 4420, "0x1144"),
  (2, 4452, "0x1164"),
]

def hexPadded_kats_ok : Bool :=
  hexPadded_kats.all fun (pad, n, want) => hexPaddedFilter pad n = want

def hexPadded_zeroPad_ok : Bool := hexPaddedFilter 0 0 = "0x" ∧ hexPaddedFilter 1 0 = "0x0"

/-- 'fmt_hex' on the offsets the pointer helpers actually produce, pinned to the
    artifact text: 'add(p, 0x00)' / 'add(p, 0xa0)' (Halo2Verifier.sol:329,334),
    'sub(NUM_INSTANCE_CPTR, 0x04)' (:300). -/
def fmtHex_kats : List (Int × String) := [
  (0, "0x00"),
  (160, "0xa0"),
  (4, "0x04"),
  (9728, "0x2600")
]

def fmtHex_kats_ok : Bool := fmtHex_kats.all fun (i, want) => fmtHex i = want

/-- 'impl Display for Value', five arms, each pinned to a real artifact line:
    bare identifier 'x' (:332 'mstore(add(p, 0x60), x)'),
    'add(p, 0x20)' (:330), 'sub(NUM_INSTANCE_CPTR, 0x04)' (:300),
    'sub(0, 0x20)' from the negative-integer arm (:519 'gp_mptr := sub(gp_mptr,
    0x20)' is the identifier arm; the integer arm is exercised by the
    'Value::Integer(int) if int < 0' path). -/
def printValue_kats : List (Value × String) := [
  (.integer 0, "0x00"),
  (.integer 32, "0x20"),
  (.integer (-32), "sub(0, 0x20)"),
  (.identifier "p" 0, "p"),
  (.identifier "p" 32, "add(p, 0x20)"),
  (.identifier "NUM_INSTANCE_CPTR" (-4), "sub(NUM_INSTANCE_CPTR, 0x04)")
]

def printValue_kats_ok : Bool :=
  printValue_kats.all fun (v, want) => printValue v = want

/-- 'impl Display for Word': the two load spellings, pinned to
    'calldataload(instance_cptr)' (Halo2Verifier.sol:1374) and 'mload(p)' (:337). -/
def printWord_kats_ok : Bool :=
  printWord .calldata (.identifier "instance_cptr" 0) = "calldataload(instance_cptr)"
  ∧ printWord .memory (.identifier "p" 0) = "mload(p)"
  ∧ printWord .memory (.identifier "mptr_end" (-32)) = "mload(sub(mptr_end, 0x20))"

end Midfall.Generator

#eval Midfall.Generator.hexFilter_kats_ok -- expect true
#eval Midfall.Generator.hexPadded_kats_ok -- expect true
#eval Midfall.Generator.hexPadded_zeroPad_ok -- expect true
#eval Midfall.Generator.fmtHex_kats_ok -- expect true
#eval Midfall.Generator.printValue_kats_ok -- expect true
#eval Midfall.Generator.printWord_kats_ok -- expect true
-- |
-- Conformance (exe root)
--
-- The Phase 3 conformance runner (PLAN section 5, docs/conformance-schema.md).
-- Built as `lake exe midfall-conformance`; the `lean_exe` stanza already exists in
-- `lakefile.toml` and `defaultTargets` now names it, so `lake build` compiles it and
-- a broken runner cannot hide.
--
-- Usage:
--
--   lake exe midfall-conformance [bundle-dir]
--
-- with `bundle-dir` defaulting to `fixtures/conformance/poseidon` under the Lean
-- tree. The bundle is produced by the Rust exporter:
--
--   cargo test -p halo2_solidity_verifier --features rust-verifier-trace \
--     --test conformance_export -- --nocapture
--
-- EXIT CODES ARE THE CONTRACT. 0 only when every comparison agreed and at least one
-- comparison was made; 1 on any trace mismatch; 2 when the bundle itself could not
-- be read or parsed. Hazard 6: a runner that prints `agreed` and exits 0 regardless
-- is worse than no harness, so the count of comparisons performed is printed and a
-- zero count is itself a failure.
--
-- This module is the exe root and holds only IO. The comparison logic is
-- `Midfall.Conformance.Replay`, the strict JSON loading is
-- `Midfall.Conformance.Bundle`. Both live under `Midfall/` rather than beside the exe
-- root on purpose: a `lean_exe` builds only its root module and the modules it
-- imports locally, so sibling files next to the exe root are NOT globbed into the
-- build (the `globs` key on a `[[lean_exe]]` stanza is inert) and a runner kept
-- there would silently never compile.

import Midfall.Conformance.Bundle
import Midfall.Conformance.Replay
import Midfall.Common.Json

namespace Midfall.Conformance

open Midfall

def readJsonFile (path : String) : IO JValue := do
  let txt ← IO.FS.readFile path
  match jParse txt with
  | .error e => throw (IO.userError ("conformance: cannot parse " ++ path ++ ": " ++ e))
  | .ok j => pure j

/-- Read and type-check the whole bundle. Any failure here is exit 2, not a
    mismatch: an unreadable fixture must never be reported as a disagreement
    between the port and the reference. -/
def loadBundle (dir : String) : IO (Except String Bundle) := do
  let vk ← readJsonFile (dir ++ "/vk.json")
  let inst ← readJsonFile (dir ++ "/instances.json")
  let tr ← readJsonFile (dir ++ "/trace.json")
  let proof ← IO.FS.readBinFile (dir ++ "/proof.bin")
  pure <| do
    let (committed, pubCols) ← parseInstances inst
    let vkInfo ← parseVk vk
    let trace ← parseTrace tr
    .ok { vk := vkInfo, committed := committed, publicCols := pubCols,
          proof := proof, trace := trace }

def run (dir : String) : IO UInt32 := do
  let bundle ← loadBundle dir
  match bundle with
  | .error e =>
      IO.println ("conformance: " ++ dir ++ ": " ++ e)
      pure 2
  | .ok b =>
      let r := replay b
      IO.println ("conformance replay: " ++ dir)
      IO.println ("  fixture " ++ b.trace.verdict
        ++ " (rust pairing check " ++ toString b.trace.pairingCheck ++ ")"
        ++ ", proof " ++ toString b.proof.size ++ " bytes")
      IO.println ("  compared: " ++ toString r.checks ++ " values  ("
        ++ toString r.absorbs ++ " absorbs, " ++ toString r.reads ++ " reads, "
        ++ toString r.squeezes ++ " squeezes, " ++ toString r.terms ++ " MSM terms)")
      if ! b.trace.fixtureProofMatch then
        IO.println ("  note: the exported proof differs from the committed "
          ++ "fixtures/poseidon/proof.bin, so the committed rust_trace.json is "
          ++ "compared by shape only (see the package report)")
      for f in r.failures do
        IO.println ("  FAIL " ++ f)
      if r.checks == 0 then
        IO.println "  RED: the runner compared nothing"
        pure 1
      else if r.failures.isEmpty then
        IO.println "  AGREED: every trace value matched"
        pure 0
      else
        IO.println ("  RED: " ++ toString r.failures.size
          ++ " mismatch(es) out of " ++ toString r.checks ++ " comparisons")
        pure 1

end Midfall.Conformance

def main (args : List String) : IO UInt32 :=
  Midfall.Conformance.run (args.head?.getD "fixtures/conformance/poseidon")

#!/usr/bin/env python3
# Generate Midfall/Yul/ImportSolcIR.lean from the pinned solc "ir" artifact.
#
# D-P15 (docs/design.md): the via-IR import is TEXTUAL - solc's own IR, quoted verbatim as
# yulObject% terms, with the Lean elaborator as the checker. This script is the verbatim part:
# it runs the pinned compiler, commits the artifact text beside the generated file, applies the
# two mechanical alpha-renames, and emits the Lean module and its gates.
#
# Everything the generated file claims about the artifact is measured here and re-checked at
# #eval time in Lean (D-P19: a gate reads the artifact, it does not paste a string).
#
# What is pinned:
#   * "ir", NOT "irOptimized" - PLAN section 7 validates the unoptimised IR and the
#     Yul-optimizer hop is in the trusted base (differential testing, not proved). The
#     consequence is measured and stated in the generated header: ir says memoryguard(128),
#     irOptimized says memoryguard(0x08e0), and the deployed bytecode begins
#     PUSH2 0x08e0 PUSH1 0x40 MSTORE.
#   * the compiler: solc 0.8.30, sha256 738dcdc6...dd683, at
#     proofs/solidity-verifier/.solc/solc - the same pin scripts/extract_ir_builtins.py uses.
#   * the settings: viaIR true, optimizer enabled runs 200, evmVersion cancun, metadata
#     bytecodeHash none (BASELINE.md; deployments/sepolia/moonlight-wrap/deployment.json).
#
# The two alpha-renames (decision 2 of docs/plans/P-IR-import.md). Lean's ident lexeme rejects
# the dollar sign and "end" is a reserved word, so the artifact cannot be quoted as it stands.
# Renaming at emit time was chosen over extending the vendored DSL lexer: the lexer is in
# vendor/ (outside this package's authorisation), a lexer accepting a dollar sign would make
# the DSL accept programs upstream rejects, and either way the imported names differ from the
# artifact text - so the rename has to be documented either way, and only the emit-time rename
# can be GATED from the artifact. The rule is
#
#     x |-> "solc_" + x.replace("$", "_")   if a dollar sign occurs in x or x is RESERVED
#     x |-> x                               otherwise
#
# The script aborts unless the rule is injective on the artifact's identifier set and its image
# is disjoint from the names it leaves alone.
#
# Nothing is dropped. The transform is a 1:1 token rewrite; if a construct will not elaborate
# the build fails and this script is fixed - statements are never deleted to make it pass. The
# generated file ties the imported AST back to the artifact by digest, by per-name call-site
# counts against the independently measured Midfall/Yul/ir-builtins.tsv, and by renamed-name
# coverage.
#
# Usage (from formal/):
#     python3 scripts/gen_import_solc_ir.py            # write the files
#     python3 scripts/gen_import_solc_ir.py --check    # fail if the generated file is stale
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

BS = chr(92)
NL = chr(10)
DQ = chr(34)

ROOT = pathlib.Path(__file__).resolve().parent.parent          # formal/
REPO = ROOT.parent
SOLC_DEFAULT = REPO / "proofs/solidity-verifier/.solc/solc"
SOLC_SHA256 = "738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683"
OUT_LEAN = ROOT / "Midfall" / "Yul" / "ImportSolcIR.lean"

ARTIFACTS = [
    ("Halo2Verifier",
     "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol",
     "Halo2Verifier", "verifier"),
    ("Halo2VerifyingKey",
     "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.sol",
     "Halo2VerifyingKey", "vk"),
]

SETTINGS = {
    "viaIR": True,
    "optimizer": {"enabled": True, "runs": 200},
    "evmVersion": "cancun",
    "metadata": {"bytecodeHash": "none"},
    "outputSelection": {"*": {"*": ["ir"], "": ["ir"]}},
}
SETTINGS_DOC = ("viaIR=true, optimizer.enabled=true, optimizer.runs=200, "
                "evmVersion=cancun, metadata.bytecodeHash=none")

# Lean keywords the artifact uses as Yul IDENTIFIERS. Measured, not guessed: every identifier of
# both artifacts was fed to yulE% and the rejections were collected (the report is in the
# generated header). The other Lean keywords that occur - if, for, switch, case, default,
# function, let, leave, object, code, data - appear only in grammar positions the DSL already
# handles, and "return" only as the return(...) statement, which has its own production;
# renaming those would break the quotation rather than fix it.
RESERVED = ["end"]

YUL_KEYWORDS = ["if", "for", "switch", "case", "default", "function", "let", "leave",
                "break", "continue", "object", "code", "data"]

IDENT_RE = re.compile(r"[A-Za-z_$][A-Za-z0-9_$]*")

# Measured from the ELABORATED AST, not from the artifact text: total Expr/Stmt node counts,
# top-level statement counts and identifier counts of each imported object. Gates 2 to 6 pin
# the import against the artifact; these pin THIS FILE against a hand-edit that deletes a
# statement. Re-measure by evaluating Midfall.Yul.Ir.shapeReport at #eval and pasting back.
PINS = {
    "verifier_nodes": 5229, "vk_nodes": 1642,
    "verifier_top": 28, "vk_top": 5,
    "verifier_names": 5037, "vk_names": 558,
    # literal aggregates, likewise measured from the elaborated AST
    "lv_num_count": 2068,
    "lv_num_sum": 1750937326901977666623612667226219455528541511728417536716929766574131469976978,
    "lv_str_count": 8, "lv_str_bytes": 108, "lv_str_sum": 10078, "lv_bool": 1,
    "kv_num_count": 1079,
    "kv_num_sum": 16189178311403014548454539355588231629199032355268472819124059515527964270806584,
    "kv_str_count": 3, "kv_str_bytes": 90, "kv_str_sum": 8625, "kv_bool": 0,
    "verifier_name_digest": 3939906383463826799, "vk_name_digest": 15713202309330422114,
}


def strip_comments(src):
    """Drop //-to-EOL comments and blank out string literals (the Lean gate re-implements it)."""
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            while i < n and src[i] != NL:
                i += 1
        elif c == DQ:
            j = i + 1
            while j < n and src[j] != DQ:
                if src[j] == BS:
                    j += 1
                j += 1
            i = j + 1
            out.append(" ")
        else:
            out.append(c)
            i += 1
    return "".join(out)


def needs_ren(x):
    return "$" in x or x in RESERVED


def ren(x):
    if needs_ren(x):
        return "solc_" + x.replace("$", "_")
    return x


def rename_idents(src):
    """One pass over the artifact: drop //-comments, copy string literals verbatim, rename
    every identifier token outside them. Strings must survive untouched - they carry the object
    names that dataoffset/datasize resolve, and the setimmutable/loadimmutable key.
    """
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            while i < n and src[i] != NL:
                i += 1
        elif c == DQ:
            j = i + 1
            while j < n and src[j] != DQ:
                if src[j] == BS:
                    j += 1
                j += 1
            out.append(src[i:j + 1])
            i = j + 1
        else:
            m = IDENT_RE.match(src, i)
            if m is not None:
                out.append(ren(m.group(0)))
                i = m.end()
            else:
                out.append(c)
                i += 1
    return "".join(out)


def fnv1a64(bs):
    h = 14695981039346656037
    for b in bs:
        h = ((h ^ b) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h


def check_rename(texts):
    """Abort unless the rename rule is injective and its image avoids the untouched names."""
    ids = sorted({x for t in texts.values() for x in IDENT_RE.findall(strip_comments(t))})
    images = [ren(x) for x in ids]
    if len(set(images)) != len(ids):
        dupes = sorted({x for x in images if images.count(x) > 1})
        sys.exit("gen_import_solc_ir: the rename rule is NOT injective; duplicated images: %s"
                 % dupes[:10])
    untouched = {x for x in ids if not needs_ren(x)}
    clash = sorted(untouched & {ren(x) for x in ids if needs_ren(x)})
    if clash:
        sys.exit("gen_import_solc_ir: a renamed image collides with an untouched original: %s"
                 % clash[:10])
    bad = sorted({ren(x) for x in ids if needs_ren(x)} & set(YUL_KEYWORDS))
    if bad:
        sys.exit("gen_import_solc_ir: a rename image collides with a Yul keyword: %s" % bad)
    return ids


def compile_ir(solc):
    sources = {}
    for label, rel, contract, base in ARTIFACTS:
        p = REPO / rel
        if not p.is_file():
            sys.exit("gen_import_solc_ir: missing tracked source %s" % p)
        sources[p.name] = {"content": p.read_text(encoding="utf-8")}
    payload = json.dumps({"language": "Solidity", "sources": sources, "settings": SETTINGS})
    proc = subprocess.run([str(solc), "--standard-json"], input=payload,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit("gen_import_solc_ir: solc exited %d" % proc.returncode)
    out = json.loads(proc.stdout)
    for e in out.get("errors", []):
        if e.get("severity") == "error":
            sys.exit("gen_import_solc_ir: solc error: " + e.get("formattedMessage", "")[:400])
    irs = {}
    for label, rel, contract, base in ARTIFACTS:
        ir = (out.get("contracts", {}).get(pathlib.Path(rel).name, {})
              .get(contract, {}) or {}).get("ir")
        if not ir:
            sys.exit("gen_import_solc_ir: no ir artifact for %s" % label)
        irs[label] = ir
    return irs


def object_name(ir):
    m = re.search(r"^object " + DQ + r"([^" + DQ + r"]*)" + DQ + r" \{", ir, re.M)
    if m is None:
        sys.exit("gen_import_solc_ir: no top-level object declaration in the artifact")
    return m.group(1)


def runtime_name(ir):
    m = re.search(r"^[ \t]+object " + DQ + r"([^" + DQ + r"]*)" + DQ + r" \{", ir, re.M)
    if m is None:
        sys.exit("gen_import_solc_ir: no runtime sub-object in the artifact")
    return m.group(1)


def lean_str(s):
    return DQ + s.replace(BS, BS + BS).replace(DQ, BS + DQ) + DQ

# ------------------------------------------------------------------ Lean template

# Tokens are substituted with @@NAME@@ so that Lean braces survive untouched. A literal
# backslash in the emitted Lean source is written @BS@.

TPL_HEAD = r'''-- |
-- Midfall.Yul.ImportSolcIR
--
-- GENERATED FILE - do not edit by hand. Everything below the GENERATED-BODY-BELOW marker is
-- produced by formal/scripts/gen_import_solc_ir.py from the pinned solc "ir" artifact of the
-- tracked deployed sources. Regenerate with
--
--     cd formal && python3 scripts/gen_import_solc_ir.py
--     python3 scripts/gen_import_solc_ir.py --check    # fails if this file is stale
--
-- D-P15 (docs/design.md): the via-IR import is TEXTUAL - solc's own IR, quoted as yulObject%
-- terms, with the elaborator as the checker. This module is that import, and it is what makes
-- Midfall.Lowering.RunContractIR inhabited: until now no imported object existed anywhere in
-- the tree, so every theorem whose only hypothesis was a RunContractIR was vacuously true, and
-- that is exactly why stage 4 declined to state lowering_equivalence.
--
-- ## Provenance (pinned here, re-derived by the gates at the bottom of this file)
--
--   compiler    @@VERSION@@
--   solc sha256 @@SHA@@
--   solc path   proofs/solidity-verifier/.solc/solc
--   settings    @@SETTINGS@@
--   output      ir - the PRE-optimisation textual via-IR
--
-- The standard-json payload is built in one place, scripts/gen_import_solc_ir.py, and that
-- script refuses to run against a compiler whose digest is not the one above. The artifact
-- text is committed verbatim beside this file:
--
@@ARTLIST@@
--
-- so the import is reproducible from the tracked sources and auditable against the bytes solc
-- emitted, rather than being a paste of something nobody can regenerate (hazard 1 of
-- docs/plans/P-IR-import.md).
--
-- ## DECISION 1: ir is pinned, not irOptimized - the memoryguard divergence is a stated
-- ## consequence of the trusted hop, not a defect
--
-- memoryguard survives BOTH artifacts, with a different ARGUMENT:
--
@@MEMGUARD@@
--
-- The deployed bytecode of Halo2Verifier begins PUSH2 0x08e0 PUSH1 0x40 MSTORE, which is what
-- Midfall.Generator.runtimeFreeMemoryPointerInit (Generator/Evm.lean:129) reads back, so the
-- shipped bytes agree with irOptimized and not with ir. That is deliberate: PLAN section 7
-- says irCheck validates the UNOPTIMISED IR, and the Yul-optimizer hop is explicitly in the
-- trusted base - covered by differential testing against the compiler, not proved here.
-- Pinning ir therefore puts the free-memory pointer at 0x80 where the deployed contract puts
-- it at 0x8e0. It is a memory-layout difference, and Bridge.ObsView deliberately excludes
-- memory, so it is not an observable difference at the level lowering_equivalence compares
-- at. verifierRuntime_head_is_memoryguard below states the pinned value propositionally, so
-- switching to irOptimized becomes a build failure and a decision rather than a silent drift.
-- Recorded again in docs/design.md D-P15.
--
-- ## DECISION 2: the two alpha-renames are applied at EMIT time
--
-- Lean's ident lexeme rejects the dollar sign and end is a reserved word, so the artifact
-- cannot be quoted as it stands. Emit-time renaming was chosen over extending the vendored DSL
-- lexer because (a) the lexer lives in vendor/, outside this package's authorisation; (b) a
-- lexer that accepts a dollar sign would make the DSL accept programs the upstream parser
-- rejects; and (c) either way the imported names differ from the artifact text, so the rename
-- has to be documented either way - and only the emit-time rename can be GATED from the
-- artifact. The rule is
--
--     x |-> "solc_" ++ x.replace "$" "_"      if x contains a dollar sign or x is reserved
--     x |-> x                                 otherwise
--
-- with the reserved list exactly @@RESERVED@@. That list is measured, not guessed: every
-- identifier of both artifacts was fed to yulE% and the rejections collected (@@RENCOUNT@@ of
-- @@IDCOUNT@@ distinct identifiers needed the rename). The other Lean keywords that occur in
-- the artifacts - if, let, for, switch, case, default, function, leave, object, code, data -
-- appear only in grammar positions the DSL already handles, and return only as the
-- return(...) statement, which has its own production; renaming those would break the
-- quotation rather than fix it. The mapping is auditable because the rule and the artifact are
-- both in the repo, and irRename_ok re-derives the whole mapping from the artifact text at
-- #eval time: injective, no image colliding with a name the rule leaves alone, no image that
-- is a Yul keyword, every renamed name actually present in the imported AST, and no original
-- name surviving anywhere in it.
--
-- ## What would not elaborate, and what was done about it (hazard 2)
--
@@ELABREPORT@@
--
-- ## Not in this file
--
-- irCheck (PLAN section 7) and the lowering_equivalence statement itself: this package
-- supplies the object those consume. The RunContractIR witness lives in
-- Midfall/Instances/ImportedIR.lean, because a Surface needs an AdmissiblePairing and D-P17
-- keeps Instances/ out of theorem-bearing files.
-- GENERATED-BODY-BELOW

import YulSemantics
import YulSemantics.Ast
import YulSemantics.Syntax
import YulSemantics.Dialect.EVM
import Midfall.Yul.Builtins

-- A 2,900-line Yul object is one enormous Lean term: the quotation macro builds a right-nested
-- list literal of about a thousand statements, each with nested expression lists, and the
-- default recursion budget is exhausted by the elaborator and again by the compiler. The option
-- is set for this file only - it is a property of the artifact's size, not of the project - and
-- it is the only Lean-level concession the import makes.
set_option maxRecDepth 400000

namespace Midfall.Yul.Ir
open YulSemantics YulSemantics.EVM Midfall.Yul.Builtins

/-! ### The imported objects -/
'''

# The per-artifact section is generated in a loop (see emit_lean); this is everything that
# follows the quotations. Written as a raw string so the Lean source appears verbatim.

TPL_BODY = r'''
/-! ### Reading the artifact back -/

/-- The committed artifact paths, relative to formal/, which is where lake build and
    scripts/checks.sh run. A missing file is a RED gate, never a silent true, and the
    reachability gate comes first so a moved path is diagnosed rather than matched by nothing
    (the standing D-P19 note). -/
@@ARTPATHS@@

def readIrArtifact (path : String) : IO String :=
  [path, "formal/" ++ path].foldl
    (fun (acc : IO String) (p : String) =>
      acc >>= fun got =>
        if got != "" then pure got
        else (try IO.FS.readFile p catch _ => pure ""))
    (pure "")

/-- FNV-1a over the artifact bytes. Not a cryptographic digest - the point is drift, not
    security - chosen because the file is 190 KB and folding that through the pure-Lean keccak
    of Midfall.Common at elaboration time would be slow. The sha256 of the same bytes is in
    each import doc string above for anyone who wants to check it with shasum. -/
def irDigest (s : String) : UInt64 :=
  s.toUTF8.data.foldl (fun (h : UInt64) (c : UInt8) =>
    (h ^^^ c.toUInt64) * 1099511628211) 14695981039346656037

/-- The identifier scan, re-implemented in Lean from the same specification the generator uses:
    drop slash-slash comments, blank out string literals, collect the identifier lexeme. Two
    independent lexers over one committed artifact is the point - irRename_ok compares what
    each of them sees. -/
structure IrScan where
  ids : List String
  cur : String
  inStr : Bool
  esc : Bool
  slash : Bool
  comment : Bool

def irScanInit : IrScan :=
  { ids := [], cur := "", inStr := false, esc := false, slash := false, comment := false }

def irIdentChar (c : Char) : Bool := (c.isAlpha || c.isDigit) || c == '_' || c == '$'

def irFlush (st : IrScan) : IrScan :=
  if st.cur.isEmpty then st
  else { st with cur := "", ids := st.cur :: st.ids }

def irStepDefault (st : IrScan) (c : Char) : IrScan :=
  if irIdentChar c && (!st.cur.isEmpty || c.isAlpha || c == '_' || c == '$') then
    { st with cur := st.cur.push c }
  else
    let st := irFlush st
    if c == '"' then { st with inStr := true }
      else if c == '/' then { st with slash := true }
      else st

def irStep (st : IrScan) (c : Char) : IrScan :=
  if st.comment then
    if c == '\n' then { st with comment := false } else st
  else if st.inStr then
    if st.esc then { st with esc := false }
    else if c == '\\' then { st with esc := true }
    else if c == '"' then { st with inStr := false }
    else st
  else if st.slash then
    let st := irFlush { st with slash := false }
    if c == '/' then { st with comment := true } else irStepDefault st c
  else irStepDefault st c

def irIdents (s : String) : List String :=
  (irFlush (s.toList.foldl irStep irScanInit)).ids.reverse

/-- The reserved list of DECISION 2, as data, so the gates are about the real rule. -/
def irReserved : List String := [@@RESERVEDLIST@@]

/-- Does this name need the alpha-rename? -/
def irNeedsRen (x : String) : Bool := x.contains '$' || irReserved.contains x

/-- The rename rule, character for character the generator's ren. -/
def irRen (x : String) : String :=
  if irNeedsRen x then "solc_" ++ x.replace "$" "_" else x

/-- The renamed names of one artifact, as the Lean lexer sees them. -/
def irRenamedOf (path : String) : IO (List String) := do
  pure ((irIdents (← readIrArtifact path)).eraseDups.filter irNeedsRen)

def verifierRenamed : IO (List String) := irRenamedOf verifierArtifactPath
def vkRenamed : IO (List String) := irRenamedOf vkArtifactPath

-- Every identifier the AST carries: variable references, user-call targets, function names,
-- parameters and return names.
mutual
partial def exprNames : Expr EVM.Op -> List String
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => args.flatMap exprNames
  | .call fn args => fn :: args.flatMap exprNames

partial def stmtNames : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtNames
  | .funDef n ps rs b => n :: ps ++ rs ++ b.flatMap stmtNames
  | .letDecl vs e => vs ++ (e.map exprNames).getD []
  | .assign vs e => vs ++ exprNames e
  | .cond c b => exprNames c ++ b.flatMap stmtNames
  | .switch c cs d => exprNames c ++ cs.flatMap (fun (_, b) => b.flatMap stmtNames)
      ++ (d.map (fun b => b.flatMap stmtNames)).getD []
  | .forLoop i c p b => i.flatMap stmtNames ++ exprNames c ++ p.flatMap stmtNames
      ++ b.flatMap stmtNames
  | .exprStmt e => exprNames e
  | .break | .continue | .leave => []
end

partial def objectNames (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtNames ++ (o.subObjects.map objectNames).flatten
'''

TPL_BODY2 = r'''
-- The builtin call sites, as opNames: the quantity the manifest
-- Midfall/Yul/ir-builtins.tsv counts in the artifact text. Two independent routes to the
-- same number, compared by gate 6.
mutual
partial def exprBuiltinCalls : Expr EVM.Op -> List String
  | .lit _ => []
  | .var _ => []
  | .builtin op args => opName op :: args.flatMap exprBuiltinCalls
  | .call _ args => args.flatMap exprBuiltinCalls

partial def stmtBuiltinCalls : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtBuiltinCalls
  | .funDef _ _ _ b => b.flatMap stmtBuiltinCalls
  | .letDecl _ e => (e.map exprBuiltinCalls).getD []
  | .assign _ e => exprBuiltinCalls e
  | .cond c b => exprBuiltinCalls c ++ b.flatMap stmtBuiltinCalls
  | .switch c cs d => exprBuiltinCalls c
      ++ cs.flatMap (fun (_, b) => b.flatMap stmtBuiltinCalls)
      ++ (d.map (fun b => b.flatMap stmtBuiltinCalls)).getD []
  | .forLoop i c p b => i.flatMap stmtBuiltinCalls ++ exprBuiltinCalls c
      ++ p.flatMap stmtBuiltinCalls ++ b.flatMap stmtBuiltinCalls
  | .exprStmt e => exprBuiltinCalls e
  | .break | .continue | .leave => []
end

partial def objectBuiltinCalls (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtBuiltinCalls ++ (o.subObjects.map objectBuiltinCalls).flatten

-- User-function call sites plus the definitions themselves: the manifest regex sees
-- "function f(" as one call site of f, so the AST count has to as well or gate 6 is unfair.
mutual
partial def exprUserCalls : Expr EVM.Op -> List String
  | .lit _ => []
  | .var _ => []
  | .builtin _ args => args.flatMap exprUserCalls
  | .call fn args => fn :: args.flatMap exprUserCalls

partial def stmtUserCalls : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtUserCalls
  | .funDef n ps rs b => n :: ps ++ rs ++ b.flatMap stmtUserCalls
  | .letDecl _ e => (e.map exprUserCalls).getD []
  | .assign _ e => exprUserCalls e
  | .cond c b => exprUserCalls c ++ b.flatMap stmtUserCalls
  | .switch c cs d => exprUserCalls c ++ cs.flatMap (fun (_, b) => b.flatMap stmtUserCalls)
      ++ (d.map (fun b => b.flatMap stmtUserCalls)).getD []
  | .forLoop i c p b => i.flatMap stmtUserCalls ++ exprUserCalls c
      ++ p.flatMap stmtUserCalls ++ b.flatMap stmtUserCalls
  | .exprStmt e => exprUserCalls e
  | .break | .continue | .leave => []
end

partial def objectUserCalls (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtUserCalls ++ (o.subObjects.map objectUserCalls).flatten

-- Total Expr/Stmt node count: the hand-edit detector of gate 7.
mutual
partial def exprCount : Expr EVM.Op -> Nat
  | .lit _ => 0
  | .var _ => 0
  | .builtin _ args => 1 + args.foldl (fun n a => n + exprCount a) 0
  | .call _ args => 1 + args.foldl (fun n a => n + exprCount a) 0

partial def stmtCount : Stmt EVM.Op -> Nat
  | .block b => 1 + b.foldl (fun n s => n + stmtCount s) 0
  | .funDef _ _ _ b => 1 + b.foldl (fun n s => n + stmtCount s) 0
  | .letDecl _ e => 1 + (e.map exprCount).getD 0
  | .assign _ e => 1 + exprCount e
  | .cond c b => 1 + exprCount c + b.foldl (fun n s => n + stmtCount s) 0
  | .switch c cs d => 1 + exprCount c
      + cs.foldl (fun n (_, b) => n + b.foldl (fun m s => m + stmtCount s) 0) 0
      + (match d with | none => 0 | some b => b.foldl (fun n s => n + stmtCount s) 0)
  | .forLoop i c p b => 1 + i.foldl (fun n s => n + stmtCount s) 0 + exprCount c
      + p.foldl (fun n s => n + stmtCount s) 0 + b.foldl (fun n s => n + stmtCount s) 0
  | .exprStmt e => 1 + exprCount e
  | .break | .continue | .leave => 1
end

partial def objectStmtCount (o : Object EVM.Op) : Nat :=
  o.codeBlock.foldl (fun n s => n + stmtCount s) 0
    + o.subObjects.foldl (fun n s => n + objectStmtCount s) 0

/-- Literal statistics of the imported AST: the hole the call-site gate leaves open. A call-site
    count cannot see a changed LITERAL - add(x, 1) and add(x, 2) have identical call sites - so
    the number of numeric literals, their sum, the number of string literals and their total
    byte length are pinned as well (gate 10). -/
structure LitAgg where
  numCount : Nat
  numSum : Nat
  strCount : Nat
  strBytes : Nat
  strSum : Nat
  boolCount : Nat

deriving Inhabited

def litZero : LitAgg :=
  { numCount := 0, numSum := 0, strCount := 0, strBytes := 0, strSum := 0, boolCount := 0 }

def litPlus (a b : LitAgg) : LitAgg :=
  { numCount := a.numCount + b.numCount, numSum := a.numSum + b.numSum,
    strCount := a.strCount + b.strCount, strBytes := a.strBytes + b.strBytes,
    strSum := a.strSum + b.strSum, boolCount := a.boolCount + b.boolCount }

/-- The byte sum of a string literal: strBytes alone cannot see "5" rewritten to "6", so the
    characters are summed as well. -/
def strAgg (s : String) : Nat × Nat :=
  (s.length, s.toList.foldl (fun acc c => acc + c.toNat) 0)

def litOne (l : Literal) : LitAgg :=
  match l with
  | .number n => { numCount := 1, numSum := n, strCount := 0, strBytes := 0, strSum := 0,
                   boolCount := 0 }
  | .string s => { numCount := 0, numSum := 0, strCount := 1, strBytes := (strAgg s).1,
                   strSum := (strAgg s).2, boolCount := 0 }
  | .bool _ => { numCount := 0, numSum := 0, strCount := 0, strBytes := 0, strSum := 0,
                 boolCount := 1 }

mutual
partial def exprLits : Expr EVM.Op -> LitAgg
  | .lit l => litOne l
  | .var _ => litZero
  | .builtin _ args => args.foldl (fun acc e => litPlus acc (exprLits e)) litZero
  | .call _ args => args.foldl (fun acc e => litPlus acc (exprLits e)) litZero

partial def stmtLits : Stmt EVM.Op -> LitAgg
  | .block b => b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero
  | .funDef _ _ _ b => b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero
  | .letDecl _ e => e.map exprLits |>.getD litZero
  | .assign _ e => exprLits e
  | .cond c b => litPlus (exprLits c) (b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
  | .switch c cs d =>
      cs.foldl (fun acc (_, b) => litPlus acc (b.foldl (fun m s => litPlus m (stmtLits s))
        litZero)) (litPlus (exprLits c) (match d with
        | none => litZero
        | some b => b.foldl (fun m s => litPlus m (stmtLits s)) litZero))
  | .forLoop i c p b =>
      (litPlus (i.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
        (litPlus (exprLits c)
          ((p ++ b).foldl (fun acc s => litPlus acc (stmtLits s)) litZero)))
  | .exprStmt e => exprLits e
  | .break | .continue | .leave => litZero
end

partial def objectLits (o : Object EVM.Op) : LitAgg :=
  litPlus (o.codeBlock.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
    (o.subObjects.foldl (fun acc s => litPlus acc (objectLits s)) litZero)

/-- The digest of every identifier the imported object carries, in order, separated so that a
    split cannot be faked: this is what sees an identifier edited inside the quotation. The
    call-site gate sees names that are called, the literal gate sees values, and neither sees a
    local variable renamed. -/
def objectNameDigest (o : Object EVM.Op) : UInt64 :=
  irDigest (String.join ((o.name :: objectNames o).flatMap (fun n => [n, "\n"])))

/-- The numbers PINS records, for re-measuring after a deliberate regeneration: evaluate this
    at #eval and paste the six numbers into PINS in scripts/gen_import_solc_ir.py. -/
def shapeReport : IO (List Nat) := do
  let a := objectLits verifierIr
  let b := objectLits vkIr
  pure [objectStmtCount verifierIr, objectStmtCount vkIr,
    verifierRuntime.length, vkRuntime.length,
    (objectNames verifierIr).length, (objectNames vkIr).length,
    a.numCount, a.numSum, a.strCount, a.strBytes, a.strSum, a.boolCount,
    b.numCount, b.numSum, b.strCount, b.strBytes, b.strSum, b.boolCount,
    (objectNameDigest verifierIr).toNat, (objectNameDigest vkIr).toNat]

/-! ### The prologue pin: DECISION 1, stated as a proposition -/

/-- THE PIN. The first statement of the imported deployed runtime block is exactly
    mstore(64, memoryguard(128)) - the ir value, not the irOptimized 0x08e0. This is rfl, so
    it is a build failure rather than a red gate if the artifact, the settings or the pinned
    output selection ever change. -/
theorem verifierRuntime_head_is_memoryguard :
    verifierRuntime.head? =
      some (Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])) := rfl

/-- The creation object's first statement, for the same reason: ir reserves 160 there and 128
    in the runtime, which is a fact about the artifact rather than an assumption. -/
theorem verifierCreation_head_is_memoryguard :
    verifierCreation.head? =
      some (Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 160)]])) := rfl

/-- The set/immutable pair, taken from the imported artifact rather than typed by hand: the
    creation object writes the immutable that the runtime object reads. This is the statement
    PLAN section 7's irCheck wants about immutables, at the level of the imported object - the
    run that exhibits it is in Midfall/Instances/ImportedIR.lean. -/
def importedSetImmutableSite : Option (Stmt EVM.Op) :=
  verifierCreation.find? fun
    | Stmt.exprStmt (Expr.builtin Op.setimmutable _) => true
    | _ => false

def importedLoadImmutableSites : Nat :=
  (objectBuiltinCalls verifierIr).filter (fun n => n == "loadimmutable") |>.length
'''

TPL_GATES = r'''
/-! ### Gates -/

/-- GATE 1 (reachability first): both committed artifacts exist, are non-empty, and carry the
    object names the import claims. Red if a file is moved or truncated - the failure mode that
    would otherwise leave every digest gate below comparing nothing. -/
def irArtifactsReachable_ok : IO Bool := do
@@GATE1@@

#eval irArtifactsReachable_ok               -- expect true

/-- GATE 2: THE DIGEST. Re-derive a digest of each artifact at #eval time and compare with the
    value the generator measured from the bytes solc emitted (D-P19). This is the gate that
    makes the committed artifact the artifact of record: change one byte of the .yul and this
    goes red. The byte counts are pinned alongside, because a digest alone would not tell a
    reader who does not trust the hash that the file was truncated rather than edited. -/
def irArtifactDigest_ok : IO Bool := do
@@GATE2@@

#eval irArtifactDigest_ok                   -- expect true

/-- GATE 3: the artifact's own shape, measured from the text rather than pasted: line count,
    dollar-sign count, memoryguard sites, and the number of object and data declarations. These
    are the numbers the header quotes and the ones a reader who cannot run solc can still check
    against the committed file. -/
def irArtifactShape_ok : IO Bool := do
@@GATE3@@

#eval irArtifactShape_ok                    -- expect true

/-- GATE 4: DECISION 2, auditable. The rename rule re-derived from the artifact text by the
    Lean lexer: injective, no image colliding with a name the rule leaves alone, no image that
    is a Yul keyword or a reserved word, the rename non-trivial, and every rename reversible by
    dropping the prefix. -/
def irRename_ok : IO Bool := do
  let ids := ((irIdents (← readIrArtifact verifierArtifactPath)) ++
    (irIdents (← readIrArtifact vkArtifactPath))).eraseDups
  let imgs := ids.map irRen
  let renamed := ids.filter irNeedsRen
  let untouched := ids.filter (fun x => ! irNeedsRen x)
  pure (ids.length > 1000 &&
    -- injective on the artifact's identifier set
    imgs.eraseDups.length == ids.length &&
    -- no image collides with a name the rule leaves alone
    ! (untouched.any (fun x => renamed.any (fun y => irRen y == x))) &&
    -- no RENAMED image is a Yul keyword or a Lean reserved word (the untouched names are
    -- allowed to be keywords: that is what the grammar is for)
    ! ((renamed.map irRen).any (fun x => x == "if" || x == "let" || x == "for" ||
      x == "switch" || x == "case" || x == "default" || x == "function" || x == "leave" ||
      x == "object" || x == "code" || x == "data" || x == "break" || x == "continue" ||
      x == "end" || x == "return")) &&
    -- the rename is non-trivial: the artifacts really do carry these names
    renamed.length == @@RENCOUNT@@ &&
    -- and the rule is reversible on every renamed name
    (renamed.all (fun x => irRen x == "solc_" ++ x.replace "$" "_" &&
      (irRen x).length == x.length + 5)))

#eval irRename_ok                             -- expect true

/-- GATE 5: no original name survives in the imported AST, and every renamed artifact name is
    actually present. The first conjunct catches a rename that was skipped; the second is the
    completeness direction of hazard 2 - a statement deleted to make the build pass takes its
    identifiers with it, and this goes red. -/
def irNoOriginalSurvives_ok : IO Bool := do
  let ns := objectNames verifierIr ++ objectNames vkIr
  let vr <- verifierRenamed
  let kr <- vkRenamed
  pure (ns.all (fun n => ! n.contains '$' && ! irReserved.contains n) &&
    vr.all (fun x => ns.contains (irRen x)) &&
    kr.all (fun x => ns.contains (irRen x)) &&
    -- the non-mechanical rename is exercised, not just the dollar-sign one
    ns.contains "solc_end" &&
    ns.length > 1000)

#eval irNoOriginalSurvives_ok               -- expect true

/-- GATE 6: THE ANTI-DROP GATE. Every builtin call site and every user-function site that the
    generator counted in the committed artifact text (Midfall/Yul/solc-ir-callsites.tsv, a regex
    over the text) is present in the imported AST with the same multiplicity, after the alpha-
    rename. Two independent routes to the same number - a python regex over the artifact and a
    fold over the elaborated term - and a deleted statement changes only one of them. This is
    what makes a partial import presented as a complete one a build failure. -/
def irCallSitesMatch_ok : IO Bool := do
  let rows := parseIrManifest (← readIrArtifact callsitesPath)
  let vbc := objectBuiltinCalls verifierIr
  let kbc := objectBuiltinCalls vkIr
  let vuc := objectUserCalls verifierIr
  let kuc := objectUserCalls vkIr
  let count (l : List String) (n : String) : Nat := (l.filter (fun x => x == n)).length
  let vrows := rows.filter fun r => r.artifact == "Halo2Verifier"
  let krows := rows.filter fun r => r.artifact == "Halo2VerifyingKey"
  pure ((vrows.filter fun r => r.kind == "builtin").length > 30 &&
        -- nothing unresolved: the dialect still parses every name the artifact calls
        (rows.filter fun r => r.kind == "unresolved").length == 0 &&
        (vrows.filter fun r => r.kind == "builtin").all fun r =>
          count vbc (irRen r.name) == r.sites &&
        (krows.filter fun r => r.kind == "builtin").all fun r =>
          count kbc (irRen r.name) == r.sites &&
        (vrows.filter fun r => r.kind == "user").all fun r =>
          count vuc (irRen r.name) == r.sites &&
        (krows.filter fun r => r.kind == "user").all fun r =>
          count kuc (irRen r.name) == r.sites &&
        -- and the check is not vacuous: the deployed verifier calls, through this import, the
        -- two builtins P-VEND added to the dialect
        count vbc "memoryguard" == 2 && count vbc "setimmutable" == 1 &&
        count vbc "loadimmutable" == 2 && count kbc "memoryguard" == 1)

#eval irCallSitesMatch_ok                 -- expect true

/-- GATE 9: A FINDING ABOUT THE TRACKED MANIFEST, pinned so it cannot be lost.
    Midfall/Yul/ir-builtins.tsv is not a measurement of the deployed Halo2Verifier artifact:
    scripts/extract_ir_builtins.py keys its standard-json source dict by BASENAME, and two of
    its three tracked sources are named Halo2Verifier.sol (the deployed one and the poseidon
    fixture dump), so the later entry overwrites the earlier and the rows labelled
    "Halo2Verifier" were computed from the poseidon dump. The deployed artifact has no xor site;
    the manifest claims three. This gate pins the divergence: fixing the collision and
    regenerating ir-builtins.tsv turns it red rather than leaving the story untold. It is a
    finding about that manifest, not about this import - gate 6 measures the committed artifact
    directly, and the two names P-VEND was actually about agree either way (last conjuncts). -/
def irBuiltinsManifestDiverges_ok : IO Bool := do
  let rows := parseIrManifest (← readIrManifest)
  let sites (art name : String) : Nat :=
    (rows.filter fun r => r.artifact == art && r.name == name).foldl (fun acc r => acc + r.sites) 0
  let vbc := objectBuiltinCalls verifierIr
  let count (l : List String) (n : String) : Nat := (l.filter (fun x => x == n)).length
  pure (count vbc "xor" == 0 && sites "Halo2Verifier" "xor" == 3 &&
    count vbc "memoryguard" == sites "Halo2Verifier" "memoryguard" &&
    count vbc "setimmutable" == sites "Halo2Verifier" "setimmutable" &&
    count vbc "loadimmutable" == sites "Halo2Verifier" "loadimmutable")

#eval irBuiltinsManifestDiverges_ok       -- expect true

/-- GATE 7: structural shape of the imported objects - names, sub-objects, data segments, and
    the elaborated node counts. The node counts are pinned from the AST this file elaborated to
    (gates 2 to 6 are what tie it to the artifact), so what they protect is a hand-edit of THIS
    file: any statement removed changes one of them. -/
def irShape_ok : Bool :=
  verifierIr.name == "@@VOBJ@@" &&
    vkIr.name == "@@KOBJ@@" &&
    verifierIr.subObjects.map (fun o => o.name) == ["@@VRT@@"] &&
    vkIr.subObjects.map (fun o => o.name) == ["@@KRT@@"] &&
    verifierIr.dataSegs.isEmpty && vkIr.dataSegs.isEmpty &&
    verifierRuntimeObject.dataSegs.map (fun d => d.1) == [".metadata"] &&
    vkRuntimeObject.dataSegs.map (fun d => d.1) == [".metadata"] &&
    ! verifierRuntime.isEmpty && ! vkRuntime.isEmpty &&
    objectStmtCount verifierIr == @@VN@@ &&
    objectStmtCount vkIr == @@KN@@ &&
    verifierRuntime.length == @@VT@@ &&
    vkRuntime.length == @@KT@@ &&
    (objectNames verifierIr).length == @@VNAME@@ &&
    (objectNames vkIr).length == @@KNAME@@ &&
    -- the immutable pair is present in the imported object, not merely in the dialect
    importedSetImmutableSite.isSome && importedLoadImmutableSites == 2 &&
    -- and every identifier of the quotation, in order: this is what sees a local variable
    -- renamed, which neither the call-site gate nor the literal gate can see
    objectNameDigest verifierIr == (@@VNDIG@@ : UInt64) &&
    objectNameDigest vkIr == (@@KNDIG@@ : UInt64)

#eval irShape_ok                            -- expect true

/-- GATE 8: the imported runtime starts with the prologue the header says it starts with,
    checked against the quotation rather than against a hand-typed copy of it. -/
def irPrologueIsTheImportedHead : Bool :=
  SyntaxEq.stmtsBeq [verifierRuntime.head?.getD Stmt.leave]
    [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])] &&
  SyntaxEq.stmtsBeq [vkRuntime.head?.getD Stmt.leave]
    [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]

#eval irPrologueIsTheImportedHead         -- expect true

/-- GATE 10: the literals. The call-site gate sees names, not values, so a changed numeric
    literal - add(x, 1) rewritten to add(x, 2), or the memoryguard reservation edited - would
    pass it. The count and sum of every numeric literal, the count and total byte length of
    every string literal, and the count of boolean literals are pinned here for both objects. -/
def irLiterals_ok : Bool :=
  let a := objectLits verifierIr
  let b := objectLits vkIr
  a.numCount == @@LVN@@ && a.numSum == @@LVS@@ && a.strCount == @@LVSC@@ &&
    a.strBytes == @@LVSB@@ && a.strSum == @@LVSS@@ && a.boolCount == @@LVBC@@ &&
    b.numCount == @@KVN@@ && b.numSum == @@KVS@@ && b.strCount == @@KVSC@@ &&
    b.strBytes == @@KVSB@@ && b.strSum == @@KVSS@@ && b.boolCount == @@KVBC@@

#eval irLiterals_ok                         -- expect true

/-! ### Axiom audit -/

-- D-P15's checker is the elaborator, so the imported terms must carry no assumptions of
-- their own. Expected: [propext, Classical.choice, Quot.sound] - the three the quotation
-- macro leaves behind - and in particular NO sorryAx.
#print axioms Midfall.Yul.Ir.verifierIr
#print axioms Midfall.Yul.Ir.vkIr
#print axioms Midfall.Yul.Ir.verifierRuntime_head_is_memoryguard

end Midfall.Yul.Ir
-- GENERATED-BODY-ABOVE
'''


BT = chr(96)


def q(s):
    """Backtick-quote a fragment for the generated Lean header comment."""
    return BT + s + BT


def comment_block(lines):
    return NL.join(("-- " + l).rstrip() for l in lines)


def emit_lean(version_line, arts, notes):
    subs = {
        "@@VERSION@@": version_line,
        "@@SHA@@": SOLC_SHA256,
        "@@SETTINGS@@": SETTINGS_DOC,
        "@@ARTLIST@@": comment_block([
            "* %s - the ir of %s: %d lines, %d bytes, %d dollar signs, sha256 %s"
            % (q(a["yul_path"]), q(a["source"]), a["lines"], a["bytes"], a["dollars"],
               q(a["sha256"]))
            for a in arts]),
        "@@MEMGUARD@@": comment_block([
            "* %s: ir says memoryguard(%s); irOptimized says memoryguard(%s)%s"
            % (q(a["label"]), a["ir_mg"], a["iro_mg"],
               " - the optimizer folds it out entirely" if a["iro_mg"] == "-" else "")
            for a in arts]),
        "@@RESERVED@@": " and ".join(q(r) for r in RESERVED),
        "@@RESERVEDLIST@@": ", ".join(lean_str(r) for r in RESERVED),
        "@@RENCOUNT@@": str(notes["renamed_total"]),
        "@@IDCOUNT@@": str(notes["id_total"]),
        "@@ELABREPORT@@": comment_block(notes["elab_report"]),
        "@@ARTPATHS@@": NL.join(
            "def %sArtifactPath : String := %s" % (a["base"], lean_str(a["yul_path"]))
            for a in arts)
            + NL + NL + "def callsitesPath : String := "
            + lean_str("Midfall/Yul/solc-ir-callsites.tsv"),
        "@@GATE1@@": NL.join("  let t%d <- readIrArtifact %sArtifactPath" % (i, a["base"]) for i, a in enumerate(arts)) + NL + "  pure (" + (" &&" + NL + "    ").join(
            "(t%d.utf8ByteSize > 1000 && t%d.contains %s && t%d.contains %s)"
            % (i, i, lean_str("object " + DQ + a["object"] + DQ + " {"), i,
               lean_str("object " + DQ + a["runtime"] + DQ + " {"))
            for i, a in enumerate(arts)) + ")",
        "@@GATE2@@": NL.join("  let t%d <- readIrArtifact %sArtifactPath" % (i, a["base"]) for i, a in enumerate(arts)) + NL + "  pure (" + (" &&" + NL + "    ").join(
            "irDigest t%d == (%s : UInt64) && t%d.utf8ByteSize == %d"
            % (i, str(a["fnv"]), i, a["bytes"]) for i, a in enumerate(arts)) + ")",
        "@@GATE3@@": NL.join("  let t%d <- readIrArtifact %sArtifactPath" % (i, a["base"]) for i, a in enumerate(arts)) + NL + "  pure (" + (" &&" + NL + "    ").join(
            x for i, a in enumerate(arts) for x in [
                ("(t%d.splitOn " + DQ + BS + "n" + DQ + ").length == %d") % (i, a["lines"]),
                ("(t%d.splitOn " + DQ + "$" + DQ + ").length - 1 == %d") % (i, a["dollars"]),
                ("(t%d.splitOn " + DQ + "memoryguard" + DQ + ").length - 1 == %d")
                % (i, a["mg_occ"]),
                ("(t%d.splitOn " + DQ + "object " + BS + DQ + DQ + ").length - 1 == %d")
                % (i, a["obj_occ"]),
                ("(t%d.splitOn " + DQ + "data " + BS + DQ + DQ + ").length - 1 == %d")
                % (i, a["data_occ"])]) + ")",
        "@@VN@@": str(PINS["verifier_nodes"]),
        "@@KN@@": str(PINS["vk_nodes"]),
        "@@VT@@": str(PINS["verifier_top"]),
        "@@KT@@": str(PINS["vk_top"]),
        "@@VNAME@@": str(PINS["verifier_names"]),
        "@@KNAME@@": str(PINS["vk_names"]),
        "@@VOBJ@@": arts[0]["object"],
        "@@KOBJ@@": arts[1]["object"],
        "@@VRT@@": arts[0]["runtime"],
        "@@KRT@@": arts[1]["runtime"],
        "@@LVN@@": str(PINS["lv_num_count"]), "@@LVS@@": str(PINS["lv_num_sum"]),
        "@@LVSC@@": str(PINS["lv_str_count"]), "@@LVSB@@": str(PINS["lv_str_bytes"]),
        "@@LVBC@@": str(PINS["lv_bool"]), "@@LVSS@@": str(PINS["lv_str_sum"]),
        "@@KVSS@@": str(PINS["kv_str_sum"]),
        "@@KVN@@": str(PINS["kv_num_count"]), "@@KVS@@": str(PINS["kv_num_sum"]),
        "@@KVSC@@": str(PINS["kv_str_count"]), "@@KVSB@@": str(PINS["kv_str_bytes"]),
        "@@KVBC@@": str(PINS["kv_bool"]),
        "@@VNDIG@@": str(PINS["verifier_name_digest"]),
        "@@KNDIG@@": str(PINS["vk_name_digest"]),
    }
    parts = [TPL_HEAD]
    for a in arts:
        parts.append(NL + "/-- " + a["doc"] + " -/" + NL + NL)
        parts.append("def %sIr : Object EVM.Op := yulObject%% " % a["base"]
                     + a["lean_text"] + NL + NL)
        parts.append("/-- The runtime sub-object name solc gives " + q(a["label"])
                     + ". Surface.irRuntime" + NL
                     + "    (Lowering/Surface.lean:467) resolves it through S.runtimeName"
                     + " ir.name, so this" + NL
                     + "    is the string a Surface must return for the imported object to be"
                     + " the one a run" + NL
                     + "    talks about. -/" + NL)
        parts.append("def %sRuntimeName : String := %s" % (a["base"], lean_str(a["runtime"]))
                     + NL + NL)
        parts.append("/-- The deployed runtime sub-object of " + a["base"] + "Ir, as an object: it"
                     + " carries the .metadata" + NL
                     + "    data segment the creation object refers to by name. The none arm is"
                     + " unreachable and" + NL
                     + "    irShape_ok is what says so. -/" + NL)
        parts.append("def %sRuntimeObject : Object EVM.Op :=" % a["base"] + NL
                     + "  match %sIr.subObject %sRuntimeName with" % (a["base"], a["base"]) + NL
                     + "  | some o => o" + NL
                     + "  | none => %sIr" % a["base"] + NL + NL)
        parts.append("/-- The deployed runtime block: the block RunContractIR runs. -/" + NL)
        parts.append("def %sRuntime : Block EVM.Op := Object.codeBlock %sRuntimeObject"
                     % (a["base"], a["base"]) + NL + NL)
        parts.append("/-- The creation object code block: where setimmutable lives. The deployed"
                     + " side" + NL
                     + "    only ever reads immutables, through loadimmutable. -/" + NL)
        parts.append("def %sCreation : Block EVM.Op := Object.codeBlock %sIr"
                     % (a["base"], a["base"]) + NL)
    parts.append(TPL_BODY)
    parts.append(TPL_BODY2)
    parts.append(TPL_GATES)
    text = "".join(parts)
    for k, v in subs.items():
        text = text.replace(k, v)
    if "@@" in text:
        sys.exit("gen_import_solc_ir: an unsubstituted token was left in the generated file")
    return text


def mg_args(text):
    """The memoryguard arguments an artifact carries, as a display string."""
    a = sorted(set(re.findall(r"memoryguard\(([0-9a-fx]+)", text)))
    return ", ".join(a) if a else "-"


EVMOP = ROOT / "vendor" / "yul-semantics" / "YulSemantics" / "Dialect" / "EVMOp.lean"
CALLSITES = ROOT / "Midfall" / "Yul" / "solc-ir-callsites.tsv"
CALL_RE = re.compile(r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\(")
FUNC_RE = re.compile(r"function\s+([A-Za-z_$][A-Za-z0-9_$]*)")
PARSE_RE = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"\s*=>\s*some')


def dialect_names():
    """The source names EVM.parse resolves, scraped from the vendored file (not duplicated)."""
    text = EVMOP.read_text(encoding="utf-8")
    m = re.search(r"def parse[\s\S]*?\| _ => none", text)
    if m is None:
        sys.exit("gen_import_solc_ir: could not find the parse table in " + str(EVMOP))
    return set(PARSE_RE.findall(m.group(0)))


def callsite_rows(label, ir):
    """Per-name call sites in the artifact text: the independent half of gate 6.

    This is deliberately the same KIND of measurement scripts/extract_ir_builtins.py makes, but
    taken from the committed artifact rather than from a solc run whose source dict keys the
    two Halo2Verifier.sol files (deployments and the poseidon fixture dump) on the same
    basename - see the finding recorded in the generated header.
    """
    text = strip_comments(ir)
    defs = set(FUNC_RE.findall(text))
    names = dialect_names()
    calls = {}
    for m in CALL_RE.finditer(text):
        n = m.group(1)
        if n in YUL_KEYWORDS:
            continue
        calls[n] = calls.get(n, 0) + 1
    rows = []
    for n in sorted(calls):
        kind = "builtin" if n in names else ("user" if n in defs else "unresolved")
        rows.append((label, kind, n, str(calls[n])))
    return rows


def write_callsites(irs):
    lines = [
        "# Measured by formal/scripts/gen_import_solc_ir.py from the committed artifacts.",
        "# Do not edit by hand. columns: artifact <TAB> kind <TAB> name <TAB> call-sites",
        "# kind: builtin = YulSemantics.EVM.parse resolves it; user = a function definition in",
        "#       the same artifact; unresolved = a dialect gap (must be empty).",
        "# Names are the ARTIFACT spellings (with dollar signs); the generated Lean file",
        "# compares them after applying its own irRen.",
    ]
    for label, ir in irs.items():
        lines += ["\t".join(r) for r in callsite_rows(label, ir)]
    CALLSITES.write_text(NL.join(lines) + NL, encoding="utf-8")


def doc_text(rel, contract, obj, rt, raw):
    b = raw.encode("utf-8")
    return ("The ir artifact of " + rel + ", contract " + contract + ": solc textual"
            + NL + "    via-IR, imported verbatim as a yulObject% quotation except for the two"
            + NL + "    alpha-renames documented in this file header. Top-level object "
            + DQ + obj + DQ + ", runtime sub-object" + NL + "    " + DQ + rt + DQ + "."
            + NL + NL + "    sha256 of the committed artifact: "
            + hashlib.sha256(b).hexdigest()
            + NL + "    FNV-1a-64: " + str(fnv1a64(b)) + "   bytes: " + str(len(b))
            + "   lines: " + str(raw.count(NL) + 1)
            + "   dollar signs: " + str(raw.count("$")))


def measure_constructs(raw):
    st = strip_comments(raw)
    toks = IDENT_RE.findall(st)
    return {
        "comment_lines": sum(1 for L in raw.split(NL) if L.strip().startswith("//")),
        "dollars": raw.count("$"),
        "dollar_ids": len(set(x for x in toks if "$" in x)),
        "end_sites": len([x for x in toks if x == "end"]),
        "u256_ann": len(re.findall(r":\s*u256", st)) + len(re.findall(r"->\s*u256", st)),
        "hexlits": raw.count("hex" + DQ),
        "true_sites": len([x for x in toks if x == "true"]),
        "return_sites": len([x for x in toks if x == "return"]),
    }


def elab_report(arts):
    """The header section hazard 2 asks for: what would not elaborate, and what was done."""
    def g(a, k):
        return a["constructs"][k]
    def each(k, unit):
        return ", ".join("%s %d %s" % (a["label"], g(a, k), unit) for a in arts)
    return [
        "Every construct the DSL cannot parse was found by elaborating the artifact, not by",
        "reading the grammar. What the measurement found, per artifact:",
        "",
        "* //-comments and the /// @src / /// @use-src annotations, for which the DSL has no",
        "  production: " + each("comment_lines", "lines") + ". Stripped at emit time.",
        "* the dollar sign in identifiers, which Lean's ident lexeme rejects: "
        + ", ".join("%s %d occurrences in %d distinct names"
                    % (a["label"], g(a, "dollars"), g(a, "dollar_ids")) for a in arts)
        + ". Renamed by the rule above.",
        "* the bare identifier end, which Lean reserves and solc uses as a parameter and return",
        "  name: " + each("end_sites", "sites") + ". Renamed by the rule above.",
        "* the type annotations : u256 and -> u256, which the DSL documents as unsupported: "
        + each("u256_ann", "occurrences")
        + " - so that documented deferral is not reached by this import. Measured, not hoped.",
        "* hex string literals: " + each("hexlits", "occurrence(s)")
        + " per artifact, every one of them a data segment, which the DSL does support.",
        "* true as an identifier: " + each("true_sites", "site(s)")
        + ", each a Yul boolean literal that the DSL maps to Literal.bool - no rename needed.",
        "* return: " + each("return_sites", "site(s)")
        + ", every one the return(...) statement, which has its own production, so it is not",
        "  renamed either and the reserved list stays exactly [end].",
        "",
        "Reconciliation with the numbers docs/plans/P-VEND-dialect.md quotes: those were taken",
        "from the DEPLOYED RUNTIME OBJECT alone (2,614 lines, 4,547 dollar signs, 6 end sites).",
        "This import takes the whole ir object - creation plus deployed - because RunContractIR",
        "reaches the runtime through Surface.irRuntime on the top-level object and because the",
        "creation side is where setimmutable lives: 2,898 lines, 4,580 dollar signs, 11 end",
        "sites, 514 distinct dollar names. The two sets of numbers describe nested artifacts,",
        "not competing measurements.",
        "",
        "NOTHING WAS DELETED TO MAKE THE BUILD PASS. The quotation below is the whole artifact,",
        "comment-stripped and renamed; gates 2, 5, 6, 8 and 10 are what goes red if it were not -",
        "gate 6 sees a deleted call, gate 8 sees a deleted node or a renamed identifier, gate 10",
        "sees an edited literal. scripts/perturb_import_ir.py runs those controls on copies",
        "outside the tree (R-41, R-54) and prints which gate reddens for which mutation. If a",
        "future solc or a future template emits a construct the DSL cannot parse, this script's",
        "output stops elaborating and the build fails loudly rather than importing less.",
    ]


def compile_extra(solc):
    """The irOptimized memoryguard arguments, measured for the header only (never imported)."""
    s = dict(SETTINGS)
    s["outputSelection"] = {"*": {"*": ["irOptimized"], "": []}}
    sources = {(REPO / rel).name: {"content": (REPO / rel).read_text(encoding="utf-8")}
               for _, rel, _, _ in ARTIFACTS}
    payload = json.dumps({"language": "Solidity", "sources": sources, "settings": s})
    out = json.loads(subprocess.run([str(solc), "--standard-json"], input=payload,
                                    capture_output=True, text=True).stdout)
    res = {}
    for label, rel, contract, base in ARTIFACTS:
        t = (out.get("contracts", {}).get(pathlib.Path(rel).name, {})
             .get(contract, {}) or {}).get("irOptimized", "")
        res[label] = mg_args(t)
    return res


def scan_dsl_rejections():
    """Feed every identifier of both artifacts to yulE% and report what Lean rejects.

    This is how the reserved list is MEASURED. One Lean process per identifier, because a parse
    error inside a quotation makes the command parser swallow following lines, so batching
    under-reports badly (it reported 97 of 514 when run as one file).
    """
    import tempfile
    solc = SOLC_DEFAULT
    irs = compile_ir(solc)
    ids = sorted({x for t in irs.values() for x in IDENT_RE.findall(strip_comments(t))})
    kw = set(YUL_KEYWORDS)
    cands = [x for x in ids if x not in kw]
    bad = []
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)
        for x in cands:
            f = tdp / "t.lean"
            f.write_text("import YulSemantics" + NL + "import YulSemantics.Syntax" + NL
                         + "open YulSemantics" + NL + "#check (yulE% " + x + ")" + NL,
                         encoding="utf-8")
            r = subprocess.run(["lake", "env", "lean", str(f)], capture_output=True, text=True,
                               cwd=str(ROOT))
            if r.returncode != 0:
                bad.append(x)
    print("identifiers fed to yulE%%: %d" % len(cands))
    print("rejected: %d" % len(bad))
    print("rejected without a dollar sign: %s" % [x for x in bad if "$" not in x])
    print("rejected with a dollar sign: %d distinct" % len([x for x in bad if "$" in x]))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solc", default=str(SOLC_DEFAULT))
    ap.add_argument("--check", action="store_true", help="fail if the generated file is stale")
    ap.add_argument("--scan", action="store_true",
                    help="measure which identifiers the DSL lexer rejects, and exit")
    args = ap.parse_args()

    if args.scan:
        scan_dsl_rejections()
        return 0

    solc = pathlib.Path(args.solc)
    if not solc.is_file():
        sys.exit("gen_import_solc_ir: no solc at %s (run "
                 "proofs/solidity-verifier/scripts/install_pinned_solc.sh)" % solc)
    digest = hashlib.sha256(solc.read_bytes()).hexdigest()
    if digest != SOLC_SHA256:
        sys.exit("gen_import_solc_ir: %s has sha256 %s, BASELINE.md pins %s"
                 % (solc, digest, SOLC_SHA256))
    version = subprocess.run([str(solc), "--version"], capture_output=True, text=True).stdout
    ver_line = " / ".join(version.strip().split(NL)[1:])

    irs = compile_ir(solc)
    iros = compile_extra(solc)
    write_callsites(irs)
    ids = check_rename(irs)
    renamed = sorted(x for x in ids if needs_ren(x))

    arts = []
    for label, rel, contract, base in ARTIFACTS:
        ir = irs[label]
        obj, rt = object_name(ir), runtime_name(ir)
        yul_path = "Midfall/Yul/solc-ir-%s.yul" % label
        (ROOT / yul_path).write_text(ir, encoding="utf-8")
        raw = ir
        ncomment = sum(1 for L in raw.split(NL) if L.strip().startswith("//"))
        arts.append({
            "label": label, "base": base, "source": rel, "yul_path": yul_path,
            "object": obj, "runtime": rt,
            "lines": raw.count(NL) + 1, "bytes": len(raw.encode("utf-8")),
            "fnv": fnv1a64(raw.encode("utf-8")),
            "sha256": hashlib.sha256(raw.encode("utf-8")).hexdigest(),
            "dollars": raw.count("$"),
            "mg_occ": raw.count("memoryguard"),
            "obj_occ": raw.count("object " + DQ),
            "data_occ": raw.count("data " + DQ),
            "ir_mg": mg_args(raw),
            "iro_mg": iros.get(label, "?"),
            "ncomment": ncomment,
            "constructs": measure_constructs(raw),
            "lean_text": rename_idents(raw).rstrip(NL),
            "doc": doc_text(rel, contract, obj, rt, raw),
        })

    notes = {
        "renamed_total": len(renamed),
        "id_total": len(ids),
        "elab_report": elab_report(arts),
    }
    text = emit_lean(ver_line, arts, notes)
    dest = OUT_LEAN
    if args.check:
        old = dest.read_text(encoding="utf-8") if dest.exists() else None
        if old != text:
            sys.exit("gen_import_solc_ir: %s is stale; re-run without --check" % dest)
        print("gen_import_solc_ir: %s is up to date" % dest)
        return 0
    dest.write_text(text, encoding="utf-8")
    print("wrote %s (%d lines)" % (dest, text.count(NL)))
    for a in arts:
        print("  %-18s %s lines=%d bytes=%d fnv=%d sha256=%s"
              % (a["label"], a["object"], a["lines"], a["bytes"], a["fnv"], a["sha256"][:16]))
    print("  renamed identifiers: %d of %d distinct" % (len(renamed), len(ids)))
    print("  reserved (non-dollar) renames: %s" % [x for x in renamed if "$" not in x])
    return 0


if __name__ == "__main__":
    sys.exit(main())

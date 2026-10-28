#!/usr/bin/env python3
"""Measure which builtins the deployed via-IR calls, and whether the dialect can parse them.

Why this exists (P-VEND, docs/plans/P-VEND-dialect.md). The IR of record is solc's *textual
via-IR*, imported verbatim as generated `yul%` quotations - design decision D-P15. A call whose
name `YulSemantics.EVM.parse` does not resolve elaborates to a USER-FUNCTION call
(`mkCall`, EVMOp.lean), which has no `Step` derivation, so any run of the imported program is
stuck there. That is what made `RunContractIR` uninhabited, and it is why the claim "the dialect
resolves every builtin the artifact calls" has to be a measurement, not an assumption.

What it does:
  1. compiles the tracked deployed sources with the PINNED compiler and the PINNED triple
     (solc 0.8.30, viaIR true, optimizer enabled runs 200, evmVersion cancun, metadata
     bytecodeHash none - BASELINE.md "Toolchain and build profile" and
     deployments/sepolia/moonlight-wrap/deployment.json `compiler`),
  2. takes the `ir` artifact per contract (D-P15 pins `ir`, the pre-optimisation via-IR text),
  3. collects every called name, stripping comments and string literals first,
  4. classifies each name as `builtin` (resolved by `parse`), `user` (a `function` definition in
     the same artifact), or `unresolved` (neither - i.e. a dialect gap),
  5. writes the manifest the Lean gate reads at #eval time (D-P19: gates read the artifact
     rather than a pasted string).

The `parse` name set is SCRAPED FROM THE VENDORED SOURCE, not duplicated here, so the manifest
cannot quietly drift away from the dialect it is measuring.

Usage (from `formal/`):
    python3 scripts/extract_ir_builtins.py
    python3 scripts/extract_ir_builtins.py --solc ../proofs/solidity-verifier/.solc/solc

Exit status is non-zero if any name is unresolved, so this doubles as a CI probe.
"""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent          # formal/
REPO = ROOT.parent                                            # repo root
SOLC_DEFAULT = REPO / "proofs/solidity-verifier/.solc/solc"
# BASELINE.md: sha256 of the pinned solc-macosx-amd64-v0.8.30+commit.73712a01.
SOLC_SHA256 = "738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683"
OUT_DEFAULT = ROOT / "Midfall" / "Yul" / "ir-builtins.tsv"
EVMOP = ROOT / "vendor" / "yul-semantics" / "YulSemantics" / "Dialect" / "EVMOp.lean"

# (artifact label, source path, contract name). The first two are the deployed pair of record;
# the poseidon dump is the current-generator reference (docs/REVIEW.md R-36: the deployed
# sources predate the curated templates, so measuring only them could miss a name the generator
# has started to emit).
ARTIFACTS = [
    ("Halo2Verifier",
     "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol",
     "Halo2Verifier"),
    ("Halo2VerifyingKey",
     "proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.sol",
     "Halo2VerifyingKey"),
    ("poseidon.Halo2Verifier",
     "proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol",
     "Halo2Verifier"),
]

# Yul keywords that are never a call target.
KEYWORDS = {"if", "for", "switch", "case", "default", "function", "let", "leave",
            "break", "continue", "object", "code", "data"}

CALL_RE = re.compile(r"([A-Za-z_$][A-Za-z0-9_$]*)\s*\(")
FUNC_RE = re.compile(r"function\s+([A-Za-z_$][A-Za-z0-9_$]*)")
PARSE_RE = re.compile(r'"([A-Za-z_][A-Za-z0-9_]*)"\s*=>\s*some')


def dialect_names():
    """The source names `YulSemantics.EVM.parse` resolves, scraped from the vendored file."""
    text = EVMOP.read_text(encoding="utf-8")
    m = re.search(r"def parse[\s\S]*?\| _ => none", text)
    if m is None:
        sys.exit("extract_ir_builtins: could not find `def parse ... | _ => none` in " + str(EVMOP))
    return set(PARSE_RE.findall(m.group(0)))


def strip_comments_and_strings(src):
    """Blank out `// ...` comments and string literals so no call name is invented from prose.

    solc's IR carries `//` comments lifted from the Solidity source (including text inside
    `assembly` blocks), and D-P15's first scan mistook some of them for calls.
    """
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == "/" and i + 1 < n and src[i + 1] == "/":
            while i < n and src[i] != "\n":
                i += 1
        elif c == '"':
            i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\":
                    i += 1
                i += 1
            i += 1
            out.append(" ")
        else:
            out.append(c)
            i += 1
    return "".join(out)


def compile_ir(solc, sources):
    settings = {
        "viaIR": True,
        "optimizer": {"enabled": True, "runs": 200},
        "evmVersion": "cancun",
        "metadata": {"bytecodeHash": "none"},
        "outputSelection": {"*": {"*": ["ir"], "": ["ir"]}},
    }
    payload = json.dumps({"language": "Solidity", "sources": sources, "settings": settings})
    proc = subprocess.run([str(solc), "--standard-json"], input=payload,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit("extract_ir_builtins: solc exited %d\n%s" % (proc.returncode, proc.stderr[:2000]))
    return json.loads(proc.stdout)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--solc", default=str(SOLC_DEFAULT))
    ap.add_argument("--out", default=str(OUT_DEFAULT))
    ap.add_argument("--allow-solc-mismatch", action="store_true",
                    help="do not fail when the compiler digest is not the pinned one")
    args = ap.parse_args()

    solc = pathlib.Path(args.solc)
    if not solc.is_file():
        sys.exit("extract_ir_builtins: no solc at %s (run "
                 "proofs/solidity-verifier/scripts/install_pinned_solc.sh)" % solc)
    digest = hashlib.sha256(solc.read_bytes()).hexdigest()
    version = subprocess.run([str(solc), "--version"], capture_output=True, text=True).stdout
    if digest != SOLC_SHA256:
        msg = ("extract_ir_builtins: %s has sha256 %s, BASELINE.md pins %s"
               % (solc, digest, SOLC_SHA256))
        if not args.allow_solc_mismatch:
            sys.exit(msg + "\n(pass --allow-solc-mismatch to measure anyway)")
        print("WARNING: " + msg, file=sys.stderr)

    names = dialect_names()
    sources, wanted = {}, []
    for label, rel, contract in ARTIFACTS:
        path = REPO / rel
        if not path.is_file():
            sys.exit("extract_ir_builtins: missing tracked source %s" % path)
        sources[path.name] = {"content": path.read_text(encoding="utf-8")}
        wanted.append((label, path.name, contract))

    out = compile_ir(solc, sources)
    for e in out.get("errors", []):
        if e.get("severity") == "error":
            sys.exit("extract_ir_builtins: solc error: " + e.get("formattedMessage", "")[:400])

    rows, unresolved_total = [], 0
    for label, srcname, contract in wanted:
        ir = (out.get("contracts", {}).get(srcname, {}).get(contract, {}) or {}).get("ir")
        if not ir:
            sys.exit("extract_ir_builtins: no `ir` artifact for %s" % label)
        text = strip_comments_and_strings(ir)
        defs = set(FUNC_RE.findall(text))
        calls = {}
        for m in CALL_RE.finditer(text):
            n = m.group(1)
            if n not in KEYWORDS:
                calls[n] = calls.get(n, 0) + 1
        for n, count in sorted(calls.items()):
            kind = "builtin" if n in names else ("user" if n in defs else "unresolved")
            if kind == "unresolved":
                unresolved_total += 1
            rows.append((label, kind, n, str(count)))

    dest = pathlib.Path(args.out)
    lines = [
        "# Measured by formal/scripts/extract_ir_builtins.py - do not edit by hand.",
        "# columns: artifact <TAB> kind <TAB> name <TAB> call-sites",
        "# kind: builtin = YulSemantics.EVM.parse resolves it; user = defined in the artifact;",
        "#       unresolved = a dialect gap (must be empty).",
        "# compiler: " + version.strip().replace("\n", " / "),
        "# triple: viaIR=true optimizer.enabled=true runs=200 evmVersion=cancun bytecodeHash=none",
    ]
    lines += ["\t".join(r) for r in rows]
    dest.write_text("\n".join(lines) + "\n", encoding="utf-8")

    builtins = sorted({r[2] for r in rows if r[1] == "builtin"})
    print("wrote %s (%d rows, %d distinct builtins)" % (dest, len(rows), len(builtins)))
    print("unresolved names: %d" % unresolved_total)
    for r in rows:
        if r[1] == "unresolved":
            print("  UNRESOLVED %s %s x%s" % (r[0], r[2], r[3]))
    for probe in ("memoryguard", "setimmutable", "loadimmutable"):
        tot = sum(int(r[3]) for r in rows if r[2] == probe)
        kinds = sorted({r[1] for r in rows if r[2] == probe})
        print("  %-14s sites=%-4d kinds=%s" % (probe, tot, kinds or ["-"]))
    return 1 if unresolved_total else 0


if __name__ == "__main__":
    sys.exit(main())

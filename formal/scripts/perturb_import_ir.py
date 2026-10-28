#!/usr/bin/env python3
"""R-41 negative controls for the P-IR import (docs/plans/P-IR-import.md).

Every mutation below is applied to a COPY of the generated import - and, where the mutation is
about the artifact, to a COPY of the artifact - under /tmp, and the #eval gates are re-run.
Nothing under the repository is modified (R-54). The point is to show that each gate reddens on
the drift it claims to catch, and to report honestly the ones that do not.

Usage (from formal/):  python3 scripts/perturb_import_ir.py
"""

import pathlib
import subprocess
import sys

FORMAL = pathlib.Path("/Users/julian/midfall/formal")
SRC = (FORMAL / "Midfall/Yul/ImportSolcIR.lean").read_text(encoding="utf-8")
ART = (FORMAL / "Midfall/Yul/solc-ir-Halo2Verifier.yul").read_text(encoding="utf-8")
SANDBOX = pathlib.Path("/tmp/midfall-perturb-import-ir")
SANDBOX.mkdir(parents=True, exist_ok=True)
DQ = chr(34)

GATES = ["1 reachable", "2 digest", "3 artifact-shape", "4 rename", "5 no-original",
         "6 callsites", "7 manifest-diverges", "8 shape+pins", "9 prologue-head",
         "10 literals"]


def run(text, tag):
    p = SANDBOX / (tag.replace("-", "_") + ".lean")
    p.write_text(text, encoding="utf-8")
    r = subprocess.run(["lake", "env", "lean", str(p)], capture_output=True, text=True,
                       cwd=str(FORMAL))
    out = (r.stdout + r.stderr)
    vals = [l.strip() for l in out.splitlines() if l.strip() in ("true", "false")]
    errs = [l for l in out.splitlines() if "error" in l.lower()]
    return {"rc": r.returncode, "values": vals, "errors": errs[:2]}


def m_delete_setimmutable(t):
    old = "setimmutable(_2, " + DQ + "5" + DQ + ", mload(128))"
    assert old in t
    return t.replace(old, "pop(0)", 1)


def m_rename_variable(t):
    old = "function round_up_to_mul_of_32(value) -> result {"
    assert old in t
    return t.replace(old, "function round_up_to_mul_of_32(valueZ) -> result {", 1)


def m_memoryguard_value(t):
    return t.replace("memoryguard(128)", "memoryguard(0x08e0)")


def m_numeric_literal(t):
    old = "add(value, 31)"
    assert old in t, "no anchor"
    return t.replace(old, "add(value, 32)", 1)


def m_string_literal(t):
    old = DQ + "AUTHORIZED_VK" + DQ
    if old in t:
        return t.replace(old, DQ + "AUTHORIZED_VJ" + DQ, 1)
    return t.replace(DQ + "5" + DQ, DQ + "6" + DQ, 1)


def m_dollar_back(t):
    i = t.index("solc_usr_")
    j = t.index(" ", i)
    return t[:i] + t[i:j].replace("_", "$", 1) + t[j:]


def m_rename_prefix_dropped(t):
    old = '  if irNeedsRen x then "solc_" ++ x.replace "$" "_" else x'
    assert old in t
    return t.replace(old, '  if irNeedsRen x then x.replace "$" "_" else x')


def m_artifact_byte(t):
    p = SANDBOX / "mutated.yul"
    p.write_text(ART.replace("memoryguard(128)", "memoryguard(129)", 1), encoding="utf-8")
    return t.replace(DQ + "Midfall/Yul/solc-ir-Halo2Verifier.yul" + DQ, DQ + str(p) + DQ)


def m_node_pin(t):
    return t.replace("objectStmtCount verifierIr ==", "objectStmtCount verifierIr == 1 +")



def m_artifact_missing(t):
    return t.replace(DQ + "Midfall/Yul/solc-ir-Halo2Verifier.yul" + DQ,
                     DQ + "/tmp/midfall-perturb-import-ir/does-not-exist.yul" + DQ)


def m_artifact_truncated(t):
    p = SANDBOX / "truncated.yul"
    lines = ART.split(chr(10))
    p.write_text(chr(10).join(lines[:-100]), encoding="utf-8")
    return t.replace(DQ + "Midfall/Yul/solc-ir-Halo2Verifier.yul" + DQ, DQ + str(p) + DQ)


def m_artifact_shape_preserved(t):
    # an edit that preserves line count, dollar count, memoryguard count and object/data count:
    # this is the one the digest catches and the coarse shape gate does NOT
    p = SANDBOX / "reshaped.yul"
    p.write_text(ART.replace("mstore(64, memoryguard(128))", "mstore(64, memoryguard(129))", 1),
                 encoding="utf-8")
    return t.replace(DQ + "Midfall/Yul/solc-ir-Halo2Verifier.yul" + DQ, DQ + str(p) + DQ)


MUTS = [
    ("baseline", lambda t: t),
    ("delete-setimmutable", m_delete_setimmutable),
    ("rename-a-variable", m_rename_variable),
    ("memoryguard-to-0x08e0", m_memoryguard_value),
    ("numeric-literal", m_numeric_literal),
    ("string-literal", m_string_literal),
    ("dollar-sign-left-in", m_dollar_back),
    ("rename-prefix-dropped", m_rename_prefix_dropped),
    ("artifact-byte-changed", m_artifact_byte),
    ("node-pin-off-by-one", m_node_pin),
    ("artifact-missing", m_artifact_missing),
    ("artifact-truncated", m_artifact_truncated),
    ("artifact-shape-preserving-edit", m_artifact_shape_preserved),
]

if __name__ == "__main__":
    base = None
    only = sys.argv[1:] or None
    for name, fn in MUTS:
        if only and name not in only:
            continue
        try:
            res = run(fn(SRC), name)
        except AssertionError as e:
            res = {"rc": None, "values": [], "errors": ["anchor missing: %s" % e]}
        if name == "baseline":
            base = res["values"]
        red = [GATES[i] for i, v in enumerate(res["values"]) if base and i < len(base) and v != base[i]]
        print("%-24s rc=%-5s nvals=%-3d reddened=%s" %
              (name, res["rc"], len(res["values"]), ",".join(red) or "NOTHING"))
        if res["errors"]:
            print("     errors: " + " | ".join(e[:130] for e in res["errors"]))

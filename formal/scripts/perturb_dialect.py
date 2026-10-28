#!/usr/bin/env python3
"""R-41 negative-control harness for the vendored EVM dialect (P-VEND).
 Mutates COPIES outside the working tree.

Nothing here writes into /Users/julian/midfall: the sources are copied to /tmp/perturb/src,
the patch is applied to the copy, the copy is compiled to /tmp/perturb/out, and the gate
file is elaborated against the perturbed build. The working tree is never touched, which
is the R-54 rule (a killed in-place harness once left .reverse deleted from
MultiPrepare.fEval).

Usage:  python3 /tmp/perturb/harness.py <case>
        python3 /tmp/perturb/harness.py list
"""
import os, pathlib, re, shutil, subprocess, sys

REPO = pathlib.Path("/Users/julian/midfall")
FORMAL = REPO / "formal"
WORK = pathlib.Path("/tmp/perturb")
SRC = WORK / "src"
OUT = WORK / "out"
LEAN = "/Users/julian/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
BASE_LEAN_PATH = subprocess.run(
    ["lake", "env", "sh", "-c", "echo $LEAN_PATH"], cwd=FORMAL,
    capture_output=True, text=True).stdout.strip()

VEND = "formal/vendor/yul-semantics/YulSemantics/Dialect"
FILES = [
    (VEND + "/EVMOp.lean",   "YulSemantics/Dialect/EVMOp"),
    (VEND + "/EVMExec.lean", "YulSemantics/Dialect/EVMExec"),
    (VEND + "/EVM.lean",     "YulSemantics/Dialect/EVM"),
    ("formal/Midfall/Yul/Builtins.lean", "Midfall/Yul/Builtins"),
]

# (name, file-basename, old, new, which gates are expected to go red)
CASES = {
  "control": [],
  "prefork": [
    (VEND + "/EVMOp.lean", "  | memoryguard | setimmutable\n", ""),
    (VEND + "/EVMOp.lean", '  | "memoryguard" => some .memoryguard | "setimmutable" => some .setimmutable\n', ""),
    (VEND + "/EVMOp.lean", '  | .memoryguard => "memoryguard" | .setimmutable => "setimmutable"\n', ""),
    (VEND + "/EVMOp.lean", "  | .datasize | .dataoffset | .loadimmutable =>\n      { deterministic := true, reads := true, writes := false, halts := false }",
                            "  | .datasize | .dataoffset | .loadimmutable =>\n      { deterministic := true, reads := true, writes := false, halts := false }"),
    (VEND + "/EVMExec.lean", "  | .memoryguard => un (fun a => a) args st\n", ""),
    (VEND + "/EVMExec.lean", """  | .setimmutable => match args with
      | [_base, k, v] => some (.ok []
          { st with env := { st.env with immutable := upd st.env.immutable k v } })
      | _ => none\n""", ""),
  ],
  "guard-not-identity": [
    (VEND + "/EVMExec.lean", "| .memoryguard => un (fun a => a) args st",
                             "| .memoryguard => un (fun a => a + 1) args st"),
  ],
  "guard-writes-memory": [
    (VEND + "/EVMExec.lean", "| .memoryguard => un (fun a => a) args st",
                             "  | .memoryguard => match args with\n"
                             "      | [a] => some (.ok [a] { st with memory := storeWord st.memory 64 a })\n"
                             "      | _ => none"),
  ],
  "setimm-swaps-key-and-value": [
    (VEND + "/EVMExec.lean", "immutable := upd st.env.immutable k v",
                             "immutable := upd st.env.immutable v k"),
  ],
  "setimm-writes-memory-not-map": [
    (VEND + "/EVMExec.lean", """      | [_base, k, v] => some (.ok []
          { st with env := { st.env with immutable := upd st.env.immutable k v } })""",
                             """      | [base, k, v] => some (.ok []
          { st with memory := storeWord st.memory base.toNat v })"""),
  ],
  "setimm-arity-lax": [
    # accept a FOURTH argument too: the gate's 4-arity stuck check must go red
    (VEND + "/EVMExec.lean", "      | [_base, k, v] => some (.ok []",
                             "      | [_base, k, v] | [_, k, v, _] => some (.ok []"),
  ],
  "guard-arity-lax": [
    # accept zero arguments: memoryguard() would then return the zero word instead of sticking
    (VEND + "/EVMExec.lean", "| .memoryguard => un (fun a => a) args st",
                             "  | .memoryguard => match args with\n"
                             "      | [a] => some (.ok [a] st)\n"
                             "      | [] => some (.ok [0] st)\n"
                             "      | _ => none"),
  ],
  "parse-drops-memoryguard": [
    (VEND + "/EVMOp.lean", '  | "memoryguard" => some .memoryguard | "setimmutable" => some .setimmutable',
                           '  | "setimmutable" => some .setimmutable'),
  ],
  "effects-memoryguard-writes": [
    (VEND + "/EVMOp.lean", """  | .memoryguard =>
      { deterministic := true, reads := false, writes := false, halts := false }""",
                           """  | .memoryguard =>
      { deterministic := true, reads := false, writes := true, halts := false }"""),
  ],
  "effects-setimm-halts": [
    (VEND + "/EVMOp.lean", """  | .setimmutable =>
      { deterministic := true, reads := false, writes := true, halts := false }""",
                           """  | .setimmutable =>
      { deterministic := true, reads := false, writes := true, halts := true }"""),
  ],
}

GATES = ["parseNewBuiltins_ok", "mkCallSplits_ok", "prologueElab_ok",
       "memoryguardStep_ok", "setimmutableStep_ok", "newEffects_ok",
       "immutablePair_ok", "irManifestReachable_ok", "irManifest_ok",
       "isWriterComposition_ok"]

def reset(use_head):
    # OUT is seeded once with a full copy of the built olean trees (vendor + Midfall) so
    # that putting it FIRST on LEAN_PATH does not hide every other module: Lean commits to
    # the first search-path root that contains the module's package directory.
    if not (OUT / "YulSemantics" / "Dialect" / "EVMOp.olean").exists():
        raise SystemExit("OUT not seeded: run  cp -R <vendor lib>/. and <main lib>/. into " + str(OUT))
    for d in (SRC,):
        if d.exists(): shutil.rmtree(d)
    SRC.mkdir(parents=True, exist_ok=True)
    # the manifest the gate reads at #eval time, so the relative path resolves from SRC/formal
    man = SRC / "formal/Midfall/Yul/ir-builtins.tsv"
    man.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(FORMAL / "Midfall/Yul/ir-builtins.tsv", man)
    for stale in OUT.rglob("*.olean"):
        if "Builtins" in str(stale):
            stale.unlink()
    for rel, _ in FILES:
        src = (REPO / rel)
        if not use_head and not src.exists(): raise SystemExit("missing " + str(src))
        if use_head and rel.startswith("formal/vendor/"):
            # the gate module is new in this package, so it only exists in the working tree;
            # the PREFORK case pairs the pristine dialect with the new gates.
            r = subprocess.run(["git", "-C", str(REPO), "show", "HEAD:" + rel],
                               capture_output=True, text=True)
            txt = r.stdout if r.returncode == 0 else src.read_text()
        else:
            txt = src.read_text()
        if not txt: raise SystemExit("empty copy for " + rel)
        if not src.exists(): raise SystemExit("missing " + str(src))
        dst = SRC / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(txt)

def apply_mutations(muts):
    for rel, old, new in muts:
        path = SRC / rel
        txt = path.read_text()
        if old not in txt:
            raise SystemExit("mutation anchor not found in %s:\n%r" % (rel, old[:120]))
        txt = txt.replace(old, new, 1)
        path.write_text(txt)

def compile_module(rel, modname):
    olean = OUT / (modname + ".olean"); ilean = OUT / (modname + ".ilean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(OUT) + os.pathsep + BASE_LEAN_PATH)
    if "yul-semantics" not in BASE_LEAN_PATH: raise SystemExit("BAD LEAN_PATH: " + BASE_LEAN_PATH[:200])
    # The vendored package has no [leanOptions] of its own, so it builds with Lean's
    # default autoImplicit=true; the Midfall package sets autoImplicit=false in its lakefile.
    opts = [] if rel.startswith("formal/vendor/") else ["-D", "autoImplicit=false"]
    p = subprocess.run([LEAN, *opts, "-D", "pp.unicode.fun=true",
                        str(SRC / rel), "-o", str(olean), "-i", str(ilean)],
                       capture_output=True, text=True, env=env, cwd=SRC / "formal")
    return p.stdout + p.stderr

def run(case):
    prefork = case == "prefork"
    if case == "control": prefork = False
    reset(prefork)
    if not prefork:
        apply_mutations(CASES[case])
    log = []
    todo = FILES if (case in ("control", "prefork") or case.startswith("effects")) \
        else [f for f in FILES if not f[0].endswith("EVM.lean")]
    for rel, mod in todo:
        out = compile_module(rel, mod)
        fails = [l for l in out.splitlines() if "error" in l]
        vals  = [(GATES[i] if i < len(GATES) else "?", l.strip())
                     for i, l in enumerate(out.splitlines())
                     if l.strip() in ("true", "false")]
        log.append((mod, fails, vals))
    return log

def main():
    if len(sys.argv) < 2 or sys.argv[1] == "list":
        for k in CASES: print(k)
        return 0
    case = sys.argv[1]
    if case not in CASES: raise SystemExit("unknown case " + case)
    log = run(case)
    red = []
    for mod, fails, vals in log:
        print("== %s: %d error lines, %d gate values" % (mod, len(fails), len(vals)))
        for f in fails[:6]: print("   ERR " + f[:200])
        for name, v in vals:
            if v == "false": red.append(name)
            else: print("   ok  " + name)
    print("RESULT %s: %s" % (case, "REDDENED: " + ", ".join(red) if red else
                             "NO GATE WENT RED (and no build failure)" if not any(f for _, f, _ in log)
                             else "build failure only"))
    return 0

main()

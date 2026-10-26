#!/usr/bin/env python3
"""Fail if any .lean file is not reachable from the Midfall root module.

Why this exists (docs/REVIEW.md R-50). kat_gate.py walks the filesystem, not the build
graph, so a module that nothing imports still contributes passing #eval gates and still
reports green, while lake build never compiles it and no later package can use it. That
happened for real: LayoutMemory.lean landed with 21 gates, checks.sh went green, and the
file was never built. Worse, the only thing that had ever elaborated it was
lake env lean, which the standing notes already flag as not applying lakefile options
(autoImplicit = false), so it accepts code the build rejects.

The fix is not to trust the next agent more. It is to make an orphaned module a hard
failure, so that "gates pass" and "code is built" stop being different claims.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MIDFALL = ROOT / "Midfall"
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)


def module_of(path):
    rel = path.relative_to(ROOT)
    return str(rel.with_suffix("")).replace("/", ".")


def collect():
    files = sorted(MIDFALL.rglob("*.lean"))
    root_file = ROOT / "Midfall.lean"
    if root_file.exists():
        files.append(root_file)
    return files


def main():
    files = collect()
    mods = {module_of(p): p for p in files}
    if "Midfall" not in mods:
        print("check_orphans: cannot find the Midfall.lean root module", file=sys.stderr)
        return 2
    deps = {
        m: [x for x in IMPORT.findall(p.read_text()) if x in mods]
        for m, p in mods.items()
    }
    seen = set()
    stack = ["Midfall"]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(deps.get(m, []))
    orphans = sorted(set(mods) - seen)
    if orphans:
        print("ORPHAN MODULES: on disk but never compiled by lake build")
        for o in orphans:
            print("  " + o + "  ->  " + str(mods[o].relative_to(ROOT)))
        print("")
        print("Register them in formal/Midfall.lean. A module nothing imports cannot be")
        print("used by any later package, and its #eval gates passing proves only that")
        print("lake env lean accepted a file the build never sees.")
        return 1
    print("ok: all %d modules are reachable from Midfall.lean" % len(mods))
    return 0


if __name__ == "__main__":
    sys.exit(main())

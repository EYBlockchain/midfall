#!/usr/bin/env python3
"""Check the two SHA-256 tables in formal/BASELINE.md.

WHY THIS EXISTS. The BASELINE fixture table used to mix tracked and untracked
rows in one list, so it half-checked: 25 of its 55 rows named files that are not
in git at all (their bytes are whatever the last test run wrote), and 2 tracked
rows had silently gone stale before the freeze and nothing noticed. This script
makes the distinction load-bearing:

  * every row under "Tracked pins" must be tracked in git AND hash-match;
  * every row under "Untracked, last-observed" must NOT be tracked (if it becomes
    tracked it belongs in the pin table, and staying here would hide that);
  * no row may appear in both tables, and every tracked fixture/dump file the
    table claims must exist on disk.

Paths in the table are relative to proofs/solidity-verifier/. Exit code is
non-zero on any failure. Run it after regenerating anything the table names:

    python3 proofs/solidity-verifier/scripts/check_baseline_pins.py
"""

import hashlib
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFIER_DIR = os.path.abspath(os.path.join(HERE, ".."))
REPO = os.path.abspath(os.path.join(VERIFIER_DIR, "..", ".."))
BASELINE = os.path.join(REPO, "formal", "BASELINE.md")

PIN_HEADING = "### Tracked pins"
OBS_HEADING = "### Untracked, last-observed"
ROW = re.compile(r"^\| ([0-9a-f]{64}) \| (.+?) \|$")


def table_rows(md, start_marker, stop_markers):
    """Rows of the first markdown sha256 table after start_marker."""
    i = md.index(start_marker)
    rest = md[i:]
    cut = len(rest)
    for m in stop_markers:
        j = rest.find(m, len(start_marker))
        if j != -1 and j < cut:
            cut = j
    rows = []
    for line in rest[:cut].splitlines():
        r = ROW.match(line.strip())
        if r:
            rows.append((r.group(1), r.group(2)))
    return rows


def main():
    if not os.path.exists(BASELINE):
        print("check_baseline_pins: no BASELINE.md at %s" % BASELINE)
        return 1
    md = open(BASELINE, encoding="utf-8").read()
    for marker in (PIN_HEADING, OBS_HEADING):
        if marker not in md:
            print("check_baseline_pins: BASELINE.md has no %r section; the table " % marker
                  + "must be split into tracked pins and untracked last-observed rows")
            return 1
    pins = table_rows(md, PIN_HEADING, ["\n### ", "\n## "])
    obs = table_rows(md, OBS_HEADING, ["\n### ", "\n## "])

    tracked = set(
        subprocess.run(
            ["git", "ls-files"], cwd=REPO, capture_output=True, text=True, check=True
        ).stdout.split()
    )

    fails, notes = [], []
    seen = set()
    for sha, path in pins + obs:
        if path in seen:
            fails.append("%s appears in both tables" % path)
        seen.add(path)

    for sha, path in pins:
        full = os.path.join(VERIFIER_DIR, path)
        gitpath = os.path.relpath(full, REPO)
        if gitpath not in tracked:
            fails.append("PIN row is not tracked in git: %s" % path)
            continue
        if not os.path.exists(full):
            fails.append("PIN row missing on disk: %s" % path)
            continue
        cur = hashlib.sha256(open(full, "rb").read()).hexdigest()
        if cur != sha:
            fails.append("PIN MISMATCH %s\n    table %s\n    disk %s" % (path, sha, cur))

    for sha, path in obs:
        full = os.path.join(VERIFIER_DIR, path)
        gitpath = os.path.relpath(full, REPO)
        if gitpath in tracked:
            fails.append("OBSERVED row is tracked - move it to the pin table: %s" % path)
            continue
        if not os.path.exists(full):
            notes.append("observed row not on disk (no run has written it): %s" % path)
            continue
        cur = hashlib.sha256(open(full, "rb").read()).hexdigest()
        if cur != sha:
            notes.append("observed row has moved since it was recorded (expected): %s" % path)

    print("check_baseline_pins: %d tracked pins, %d untracked last-observed rows" % (len(pins), len(obs)))
    for n in notes:
        print("  note: " + n)
    if fails:
        for f in fails:
            print("  FAIL: " + f)
        print("check_baseline_pins: FAILED (%d)" % len(fails))
        return 1
    print("ok: all %d tracked pins match the working tree; %d untracked rows are " % (len(pins), len(obs))
          + "correctly labelled as not pins")
    return 0


if __name__ == "__main__":
    sys.exit(main())

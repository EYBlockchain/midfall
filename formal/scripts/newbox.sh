#!/usr/bin/env bash
# newbox.sh - create a worker worktree WITHOUT the ~45 min cold build.
#
# WHY. Every worker box this session spent its first 35-58 minutes compiling a tree that was already
# compiled in another directory: about 7-8 hours of worker time. Lean .olean files contain no absolute
# paths (verified: strings on Midfall.olean finds zero /Users references), and macOS APFS clonefile
# copies a 9.1 GiB .lake in seconds at no extra disk cost. So the cache is portable: clone it, then
# let lake do a small incremental build for whatever the new branch adds.
#
# USAGE: formal/scripts/newbox.sh <branch> <path> [base-ref]   (base-ref defaults to formal/baseline)
# Then run: cd <path>/formal && lake build   -- it should be INCREMENTAL (minutes), not cold.

set -euo pipefail

BRANCH=${1:?usage: newbox.sh BRANCH PATH [BASE]}
DEST=${2:?usage: newbox.sh BRANCH PATH [BASE]}
BASE=${3:-formal/baseline}

ROOT=$(git rev-parse --show-toplevel)
SRC_LAKE=$ROOT/formal/.lake

if [ ! -d $SRC_LAKE/build/lib/lean ]; then
  echo newbox: no built oleans in the main tree - accept a cold build >&2
  SRC_LAKE=
fi

# A stale empty directory at DEST blocks git worktree add; this bit us twice.
if [ -d $DEST ]; then
  echo newbox: removing stale worktree dir $DEST >&2
  git worktree remove --force $DEST 2>/dev/null || rm -rf $DEST
fi
git worktree prune
git branch -D $BRANCH 2>/dev/null || true

echo newbox: adding worktree $DEST on $BRANCH from $BASE
git worktree add -b $BRANCH $DEST $BASE >/dev/null

# MOD7F found the FIRST build was ~13 min, not ~2, because the vendor subproject keeps its OWN
# .lake and the clone above did not include it. Clone it too if present.
if [ -d $ROOT/formal/vendor/yul-semantics/.lake ]; then
  mkdir -p $DEST/formal/vendor
  cp -Rc $ROOT/formal/vendor/yul-semantics/.lake $DEST/formal/vendor/yul-semantics/.lake 2>/dev/null \
    || cp -R $ROOT/formal/vendor/yul-semantics/.lake $DEST/formal/vendor/yul-semantics/.lake 2>/dev/null || true
  echo newbox: vendor .lake cloned
fi

if [ -n $SRC_LAKE ]; then
  T0=$(python3 -c 'import time;print(time.time())')
  if cp -Rc $SRC_LAKE $DEST/formal/.lake 2>/dev/null; then MODE=clonefile; else
    cp -R $SRC_LAKE $DEST/formal/.lake; MODE=full-copy; fi
  T1=$(python3 -c 'import time;print(time.time())')
  python3 -c "print('newbox: .lake ' + '$MODE' + ' in %.1f s' % ($T1-$T0))"
fi

# The fixture bundle is git-ignored, so a fresh worktree does not have it.
SRC=$ROOT/proofs/solidity-verifier/target/poseidon-fixture-dump
if [ -d $SRC ]; then
  DST=$ROOT/../$(basename $DEST)/proofs/solidity-verifier/target/poseidon-fixture-dump
  mkdir -p $DEST/proofs/solidity-verifier/target/poseidon-fixture-dump
  cp $SRC/*.bin $SRC/*.be $SRC/*.sol $DEST/proofs/solidity-verifier/target/poseidon-fixture-dump/ 2>/dev/null || true
  N=$(ls $DEST/proofs/solidity-verifier/target/poseidon-fixture-dump | wc -l | tr -d ' ')
  echo newbox: fixtures seeded, $N files
fi

# kat_gate.py cannot find lean without these; several confused KAT reports came from omitting them.
echo newbox: worker shells need ELAN_HOME set to HOME/.elan and HOME/.elan/bin on PATH
cd $DEST && git rev-parse --short HEAD && git branch --show-current

# NOTES
#  - Never clone a .lake that a build is currently writing. A half-written olean shows up as a FALSE
#    register red - the same failure mode as a SIGTERM-d verify.sh, seen three times this session.
#  - A cloned .lake may be stale relative to the new branch. That is fine, lake rebuilds what changed.
#    But never trust a register or cone number printed from a tree that has not run lake build since
#    it was created.

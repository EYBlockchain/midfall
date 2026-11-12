#!/usr/bin/env bash
# ram_guard.sh - measure and enforce a RAM budget for THIS process tree.
#
# WHY THIS EXISTS (D-P31, docs/plans/P-RAM.md). Two host crashes are on the record: a
# session died at 8.7 GB peak lean RSS (six native_decide in one process), and a per-unit
# native_decide reached 16.8 GB on a 32 GB machine with swap climbing past 50 GB, which
# took the host down. Both numbers lived as COMMENTS inside Midfall/Lowering/RunEmitted.lean,
# so nothing stopped the next package from repeating them. This is the enforcement half: a
# budget you can state, a wrapper that holds it, and a report line in the gate so drift is
# visible before it is fatal.
#
# THE SCOPING RULE, and why it is a tree and not a name match. A first-attempt watchdog
# summed every process named lean and therefore blamed this session for two unrelated lean
# processes already running on the host (~660 MB each). Every number here comes from the
# process tree rooted at a pid this script owns: the transitive closure over ppid from
# 'ps -axo pid,ppid,rss'. Foreign processes are not in that closure, so they are never
# counted, never blamed, and never killed.
#
# DEPENDENCY-FREE: bash 3.2 (the macOS /bin/bash), ps, awk, sysctl, vm_stat. No GNU
# coreutils assumption - this host has neither setsid nor /bin/true.
#
# USAGE
#   ram_guard.sh [options]                    report on the calling tree, exit 0
#   ram_guard.sh [options] -- CMD ARGS...     run CMD under the budget
#   ram_guard.sh --selftest                   prove the guard fires, and fires narrowly
#
# OPTIONS
#   --limit SIZE   hard budget on tree RSS in wrapper mode; the tree is killed when the
#                  sum crosses it. Default 6G. K/M/G suffixes accepted.
#   --warn SIZE    soft budget; crossing it makes the verdict TIGHT, not DANGER. Default 4G.
#   --proc-limit SIZE  budget on the LARGEST SINGLE PROCESS in the tree, not the sum.
#                      Default 6G. This is the shape of both recorded crashes: ONE lean
#                      process climbing alone. A cold parallel `lake build` legitimately
#                      sums to 16.86 GiB across ten workers while no single one passes
#                      4.28 GiB (measured, D-P31), so a build wants --proc-limit and a
#                      generous --limit, and a single heavy evaluation wants the reverse.
#   --interval SEC poll period in wrapper mode. Default 0.5.
#   --grace SEC    how long a TERM'd tree gets before KILL. Default 2.
#   --tree PID     root the tree at PID instead of the default (report: the caller;
#                  wrapper: the launched child).
#   --tree-self    root the tree at this script rather than at the caller.
#   --no-kill      observe and report but never kill.
#   --kernel       also report the kernel-measured maxrss of the run (no sampling error),
#                  via /usr/bin/time -l when it exists.
#   --json         machine-readable output.
#   --quiet, -q    one line, no banner. This is what checks.sh uses.
#   --label NAME   tag echoed in the output so a log line says who asked.
#   --strict       exit 2 on a DANGER verdict (report mode only). checks.sh does NOT use
#                  this: a report that can fail a build is a gate wearing a costume.
#   --selftest     run the three demonstrations and exit 0 iff all pass.
#   --help         this text.
#
# VERDICT, stated so it is checkable. 'avail' is (free + inactive + speculative) pages,
# i.e. what a fresh multi-GB allocation can actually take without pressure. 'tree' is this
# tree's summed RSS.
#   DANGER  avail < 25% of physical, or swap used > 50% of physical, or tree > --limit
#   TIGHT   avail < 50% of physical, or swap used > 25% of physical, or tree > --warn
#   OK      otherwise
#
# EXIT CODES
#   report mode  0, or 2 with --strict on DANGER. Never anything else.
#   wrapper mode the command's own exit code, or 137 if the guard killed it.
#   selftest     0 iff every demonstration passed.
#
# MEASURED LIMITATION, recorded rather than hidden. RSS is sampled, not traced, so a spike
# that starts and ends between two polls is missed. At --interval 0.5 a sub-half-second
# transient can survive; the 16.8 GB case was a sustained climb over minutes and is caught
# with room to spare. Use --kernel for an exact single-process peak, and a smaller
# --interval for a run whose allocation is known to be spiky.

set -u

LIMIT=6442450944     # 6 GiB
WARN=4294967296      # 4G
PROCLIMIT=6442450944 # 6 GiB per single process - the actual crash signature
INTERVAL=0.5
GRACE=2
ROOT_PID=""
TREE_SELF=0
NO_KILL=0
DO_JSON=0
DO_QUIET=0
DO_STRICT=0
DO_SELFTEST=0
DO_KERNEL=0
LABEL=""
CMD=()

usage() {
  # Print the header comment block and stop at the first non-comment line, so the help
  # text cannot fall out of date with a hardcoded line range (BSD sed has no setsid-style
  # brace-and-quit form, so this is awk).
  awk 'NR == 1 { next }
       /^#/ { sub(/^#[[:space:]]{0,1}/, ""); print; next }
       { exit }' "$0"
}
die() { printf 'ram_guard: %s\n' "$1" >&2; exit 64; }

# ---------- sizes ----------
to_bytes() {
  awk -v s="$1" 'BEGIN{
    s = toupper(s); gsub(/[ \t]/, "", s)
    m = 1
    if (s ~ /K$/)      { m = 1024;       sub(/K$/, "", s) }
    else if (s ~ /M$/) { m = 1048576;    sub(/M$/, "", s) }
    else if (s ~ /G$/) { m = 1073741824; sub(/G$/, "", s) }
    else if (s ~ /B$/) { sub(/B$/, "", s) }
    if (s !~ /^[0-9]+(\.[0-9]+)?$/) { print -1; exit }
    v = s * m
    if (v < 1) { print -1; exit }
    printf "%d\n", v
  }'
}

human() {
  awk -v b="$1" 'BEGIN{
    if (b >= 1073741824) printf "%.2f GiB", b / 1073741824
    else if (b >= 1048576) printf "%.2f MiB", b / 1048576
    else if (b >= 1024)    printf "%.2f KiB", b / 1024
    else printf "%d B", b
  }'
}

# ---------- the four numbers ----------
phys_bytes() { sysctl -n hw.memsize 2>/dev/null || echo 0; }

# Page size is read out of vm_stat itself so the two cannot disagree.
# avail = free + inactive + speculative: what a fresh allocation can actually take.
vm_bytes() {
  vm_stat 2>/dev/null | awk -v want="$1" '
    /page size of/ { for (i = 1; i <= NF; i++) if ($i ~ /^[0-9]+$/) ps = $i + 0 }
    /^Pages free:/        { free = $NF + 0 }
    /^Pages inactive:/    { inact = $NF + 0 }
    /^Pages speculative:/ { spec = $NF + 0 }
    /^Pages wired down:/  { wired = $NF + 0 }
    END {
      if (ps == 0) ps = 4096
      if (want == "free")       printf "%d\n", free * ps
      else if (want == "avail") printf "%d\n", (free + inact + spec) * ps
      else if (want == "wired") printf "%d\n", wired * ps
      else printf "%d\n", 0
    }'
}

# vm.swapusage: "total = 3072.00M  used = 2249.06M  free = 822.94M  (encrypted)"
swap_used_bytes() {
  sysctl -n vm.swapusage 2>/dev/null | awk '
    # the value is TWO fields after the word: used = 2249.06M
    { for (i = 1; i <= NF; i++) if ($i == "used") { v = $(i + 2) } }
    END {
      u = 1
      if (v ~ /K$/)      { u = 1024;       sub(/K$/, "", v) }
      else if (v ~ /M$/) { u = 1048576;    sub(/M$/, "", v) }
      else if (v ~ /G$/) { u = 1073741824; sub(/G$/, "", v) }
      if (v == "" || v + 0 != v) v = 0
      printf "%d\n", v * u
    }'
}

# ---------- the tree ----------
# "total_kb max_kb max_pid nproc" for the ppid closure of $1.
tree_stats() {
  ps -axo pid=,ppid=,rss= 2>/dev/null | awk -v root="$1" '
    { rss[$1] = $3 + 0; kids[$2] = kids[$2] " " $1 }
    END {
      n = 1; stack[1] = root + 0
      total = 0; max = 0; maxp = root; cnt = 0
      while (n > 0) {
        p = stack[n--]; cnt++
        r = rss[p] + 0; total += r
        if (r > max) { max = r; maxp = p }
        m = split(kids[p], a, " ")
        for (j = 1; j <= m; j++) if (a[j] != "") { n++; stack[n] = a[j] + 0 }
      }
      printf "%d %d %d %d\n", total, max, maxp, cnt
    }'
}

tree_pids() {
  ps -axo pid=,ppid= 2>/dev/null | awk -v root="$1" '
    { kids[$2] = kids[$2] " " $1 }
    END {
      n = 1; stack[1] = root + 0
      while (n > 0) {
        p = stack[n--]; print p
        m = split(kids[p], a, " ")
        for (j = 1; j <= m; j++) if (a[j] != "") { n++; stack[n] = a[j] + 0 }
      }
    }'
}

proc_name() {
  local n
  n=$(ps -o comm= -p "$1" 2>/dev/null | sed 's|.*/||' | tr -d '\n')
  if [ -z "$n" ]; then n='(exited)'; fi
  printf '%s' "$n"
}

# ---------- verdict ----------
verdict() {
  VERDICT=OK; REASON=""
  local phys="$1" avail="$2" swap="$3" tree="$4" limit="$5" warn="$6"
  local a25 a50
  a25=$(awk -v p="$phys" 'BEGIN{printf "%d", p * 0.25}')
  a50=$(awk -v p="$phys" 'BEGIN{printf "%d", p * 0.50}')
  if [ "$tree" -gt "$warn" ]; then VERDICT=TIGHT; REASON="tree > warn"; fi
  if [ "$avail" -lt "$a50" ]; then VERDICT=TIGHT; REASON="$REASON avail<50%phys"; fi
  if [ "$swap" -gt "$a25" ];  then VERDICT=TIGHT; REASON="$REASON swap>25%phys"; fi
  if [ "$tree" -gt "$limit" ] || [ "$avail" -lt "$a25" ] || [ "$swap" -gt "$a50" ]; then
    VERDICT=DANGER; REASON=""
    if [ "$tree" -gt "$limit" ]; then REASON="tree > limit"; fi
    if [ "$avail" -lt "$a25" ];  then REASON="$REASON avail<25%phys"; fi
    if [ "$swap" -gt "$a50" ];   then REASON="$REASON swap>50%phys"; fi
  fi
  if [ -z "$REASON" ]; then REASON="headroom above every threshold"; fi
  return 0
}

# ---------- killing, narrowly ----------
# The wrapper makes the child a process-group leader with set -m, so the group is exactly
# the subtree; the ppid closure is applied as well in case a grandchild escaped it. The
# guard is the PARENT of the root, so it is in neither set and cannot kill itself.
kill_tree() {
  local root="$1" pids p
  pids=$(tree_pids "$root")
  kill -TERM -"$root" 2>/dev/null || true
  for p in $pids; do kill -TERM "$p" 2>/dev/null || true; done
  sleep "$GRACE"
  kill -KILL -"$root" 2>/dev/null || true
  for p in $pids; do kill -KILL "$p" 2>/dev/null || true; done
  return 0
}

# ---------- report ----------
do_report() {
  local root="$1"
  local phys avail free swap stats total maxkb maxpid nproc treeb maxb
  phys=$(phys_bytes); avail=$(vm_bytes avail); free=$(vm_bytes free); swap=$(swap_used_bytes)
  stats=$(tree_stats "$root")
  total=$(printf '%s' "$stats" | awk '{print $1}')
  maxkb=$(printf '%s' "$stats" | awk '{print $2}')
  maxpid=$(printf '%s' "$stats" | awk '{print $3}')
  nproc=$(printf '%s' "$stats" | awk '{print $4}')
  treeb=$((total * 1024)); maxb=$((maxkb * 1024))
  verdict "$phys" "$avail" "$swap" "$treeb" "$LIMIT" "$WARN"
  if [ "$DO_JSON" -eq 1 ]; then
    printf '{"phys_bytes":%s,"free_bytes":%s,"avail_bytes":%s,"swap_used_bytes":%s,"tree_rss_bytes":%s,"tree_max_rss_bytes":%s,"tree_max_pid":%s,"tree_nproc":%s,"limit_bytes":%s,"warn_bytes":%s,"verdict":"%s","root":%s,"label":"%s"}\n' \
      "$phys" "$free" "$avail" "$swap" "$treeb" "$maxb" "$maxpid" "$nproc" "$LIMIT" "$WARN" "$VERDICT" "$root" "$LABEL"
    return 0
  fi
  if [ "$DO_QUIET" -eq 1 ]; then
    printf 'mem: phys %s | avail %s (free %s) | swap %s | tree %s / %s proc (max %s pid %s %s) | budget tree %s / proc %s | %s\n' \
      "$(human "$phys")" "$(human "$avail")" "$(human "$free")" "$(human "$swap")" \
      "$(human "$treeb")" "$nproc" "$(human "$maxb")" "$maxpid" "$(proc_name "$maxpid")" \
      "$(human "$LIMIT")" "$(human "$PROCLIMIT")" "$VERDICT"
    return 0
  fi
  printf 'ram_guard report (tree rooted at pid %s)\n' "$root"
  printf '  physical memory : %s (%s B)\n' "$(human "$phys")" "$phys"
  printf '  bytes free      : %s strictly free; %s available (free+inactive+speculative)\n' "$(human "$free")" "$(human "$avail")"
  printf '  swap used       : %s\n' "$(human "$swap")"
  printf '  this tree RSS   : %s across %s process(es); largest %s (pid %s %s)\n' \
    "$(human "$treeb")" "$nproc" "$(human "$maxb")" "$maxpid" "$(proc_name "$maxpid")"
  printf '  budget          : tree limit %s, warn %s, single-process limit %s\n' "$(human "$LIMIT")" "$(human "$WARN")" "$(human "$PROCLIMIT")"
  printf '  verdict         : %s (%s)\n' "$VERDICT" "$REASON"
  return 0
}

# ---------- wrapper ----------
do_wrap() {
  local child root stats total maxkb maxpid nproc treeb
  local peak=0 peak_max=0 peak_maxpid=0 peak_name='' peak_n=0 killed=0 rc=0
  local ktmp=""
  set -m
  if [ "$DO_KERNEL" -eq 1 ] && command -v /usr/bin/time >/dev/null 2>&1; then
    ktmp=$(mktemp -t ramguard)
    /usr/bin/time -l -o "$ktmp" "$@" &
  else
    "$@" &
  fi
  child=$!
  set +m
  root="$child"
  [ -n "$ROOT_PID" ] && root="$ROOT_PID"
  printf 'ram_guard: watching pid %s (%s) against a %s tree budget, poll %ss\n' \
    "$child" "$1" "$(human "$LIMIT")" "$INTERVAL" >&2
  while kill -0 "$child" 2>/dev/null; do
    stats=$(tree_stats "$root")
    total=$(printf '%s' "$stats" | awk '{print $1}')
    maxkb=$(printf '%s' "$stats" | awk '{print $2}')
    maxpid=$(printf '%s' "$stats" | awk '{print $3}')
    nproc=$(printf '%s' "$stats" | awk '{print $4}')
    treeb=$((total * 1024))
    # the name is read AT THE SAMPLE, not later: by the time the run ends the peak
    # process is usually gone and ps would report nothing.
    if [ "$treeb" -gt "$peak" ]; then peak=$treeb; peak_max=$((maxkb * 1024)); peak_maxpid=$maxpid; peak_n=$nproc; peak_name=$(proc_name "$maxpid"); fi
    procb=$((maxkb * 1024))
    BREACH=""
    if [ "$treeb" -gt "$LIMIT" ]; then BREACH="tree $(human "$treeb") > limit $(human "$LIMIT")"; fi
    if [ "$procb" -gt "$PROCLIMIT" ]; then BREACH="${BREACH:+$BREACH; }single-process $(human "$procb") > proc-limit $(human "$PROCLIMIT")"; fi
    if [ -n "$BREACH" ]; then
      if [ "$NO_KILL" -eq 1 ]; then
        printf 'ram_guard: over budget (%s); --no-kill, so leaving it alone\n' "$BREACH" >&2
      else
        printf 'ram_guard: over budget (%s) - killing pid %s and its %s descendant(s), and nothing outside that tree\n' \
          "$BREACH" "$root" "$((nproc - 1))" >&2
        kill_tree "$root" 2>/dev/null
        killed=1
        break
      fi
    fi
    sleep "$INTERVAL"
  done
  # the outer group redirect swallows bash's own 'Terminated: 15' job-control
  # notice, which is noise: the guard has already said what happened, in words.
  { wait "$child" 2>/dev/null; rc=$?; } 2>/dev/null
  local phys avail free swap
  phys=$(phys_bytes); avail=$(vm_bytes avail); free=$(vm_bytes free); swap=$(swap_used_bytes)
  verdict "$phys" "$avail" "$swap" "$peak" "$LIMIT" "$WARN"
  printf 'ram_guard: peak tree RSS %s (%s proc, largest %s at pid %s %s); budget %s; verdict %s\n' \
    "$(human "$peak")" "$peak_n" "$(human "$peak_max")" "$peak_maxpid" "$peak_name" \
    "$(human "$LIMIT")" "$VERDICT" >&2
  if [ -n "$ktmp" ]; then
    local kmax kfoot
    kmax=$(awk '/maximum resident set size/ { print $1 }' "$ktmp" 2>/dev/null)
    kfoot=$(awk '/peak memory footprint/ { print $1 }' "$ktmp" 2>/dev/null)
    if [ -n "$kmax" ]; then
      printf 'ram_guard: kernel maxrss %s (largest single process, measured, no sampling error)' \
        "$(human "$kmax")" >&2
      if [ -n "$kfoot" ]; then printf '; peak footprint %s' "$(human "$kfoot")" >&2; fi
      printf '\n' >&2
    fi
    rm -f "$ktmp"
  fi
  if [ "$killed" -eq 1 ]; then
    printf 'ram_guard: KILLED - the run exceeded its stated budget. Narrow the gate or raise the budget in docs/PLAN.md section 12; do not simply re-run it.\n' >&2
    return 137
  fi
  return "$rc"
}

# ---------- selftest: the guard must be SHOWN to fire ----------
# 1. a runaway climbing past a LOW budget inside the tree  -> must be killed (exit 137)
# 2. a well-behaved child under budget                    -> must survive untouched
# 3. a foreign allocator OUTSIDE the guarded tree         -> must NOT be killed
# 3 is the regression test for the mis-crediting bug: a name-matching watchdog would have
# killed it, and would have charged this session for its memory.
do_selftest() {
  local fails=0 rc
  local tmpd; tmpd=$(mktemp -d -t ramguard)
  cat >"$tmpd/alloc.py" <<'PYEOF'
import sys, time
step, delay, reps = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
bufs = []
for _ in range(reps):
    bufs.append(bytearray(b"x" * (step * 1024 * 1024)))
    time.sleep(delay)
time.sleep(120)
PYEOF
  local ALLOC="awk"
  if command -v python3 >/dev/null 2>&1; then ALLOC="python3 $tmpd/alloc.py"; fi
  printf 'ram_guard selftest (allocator: %s, tmp: %s)\n' "$ALLOC" "$tmpd"

  printf '  [1] runaway climbing past a 300M budget ... '
  LIMIT=$(to_bytes 300M); WARN=$(to_bytes 200M); INTERVAL=0.2; GRACE=1
  do_wrap $ALLOC 64 0.4 40 >/dev/null 2>&1
  rc=$?
  if [ "$rc" -eq 137 ]; then printf 'PASS (killed, exit 137)\n'
  else printf 'FAIL (exit %s, expected 137)\n' "$rc"; fails=$((fails + 1)); fi

  printf '  [2] well-behaved child under budget ... '
  LIMIT=$(to_bytes 6G); WARN=$(to_bytes 4G); INTERVAL=0.5; GRACE=2
  do_wrap sleep 1.5 >/dev/null 2>&1
  rc=$?
  if [ "$rc" -eq 0 ]; then printf 'PASS (exit 0, untouched)\n'
  else printf 'FAIL (exit %s, expected 0)\n' "$rc"; fails=$((fails + 1)); fi

  printf '  [3] foreign allocator outside the guarded tree ... '
  if [ "$ALLOC" = "awk" ]; then
    ( awk 'BEGIN{for(i=0;i<200000;i++)a[i]=i"xxxxxxxxxx"}'; sleep 6 ) &
  else
    $ALLOC 32 0.4 20 >/dev/null 2>&1 &
  fi
  local foreign=$!
  sleep 0.5
  do_wrap sleep 2 >/dev/null 2>&1
  rc=$?
  local alive=0; kill -0 "$foreign" 2>/dev/null && alive=1
  if [ "$rc" -eq 0 ] && [ "$alive" -eq 1 ]; then
    printf 'PASS (guarded run exit 0; foreign pid %s still alive)\n' "$foreign"
  else
    printf 'FAIL (guarded exit %s, foreign alive=%s: the guard reached outside its tree)\n' "$rc" "$alive"
    fails=$((fails + 1))
  fi
  kill -KILL "$foreign" 2>/dev/null || true
  wait "$foreign" 2>/dev/null || true
  rm -rf "$tmpd"

  if [ "$fails" -eq 0 ]; then printf 'ram_guard selftest: ALL PASS\n'; return 0; fi
  printf 'ram_guard selftest: %s FAILURE(S)\n' "$fails"; return 1
}

# ---------- arguments ----------
while [ "$#" -gt 0 ]; do
  case "$1" in
    --limit)    [ "$#" -ge 2 ] || die "--limit needs a size"; LIMIT=$(to_bytes "$2"); { [ -n "$LIMIT" ] && [ "$LIMIT" -gt 0 ]; } || die "bad --limit: $2"; shift 2 ;;
    --warn)     [ "$#" -ge 2 ] || die "--warn needs a size"; WARN=$(to_bytes "$2"); { [ -n "$WARN" ] && [ "$WARN" -gt 0 ]; } || die "bad --warn: $2"; shift 2 ;;
    --proc-limit) [ "$#" -ge 2 ] || die "--proc-limit needs a size"; PROCLIMIT=$(to_bytes "$2"); { [ -n "$PROCLIMIT" ] && [ "$PROCLIMIT" -gt 0 ]; } || die "bad --proc-limit: $2"; shift 2 ;;
    --interval) [ "$#" -ge 2 ] || die "--interval needs a number"; INTERVAL="$2"; shift 2 ;;
    --grace)    [ "$#" -ge 2 ] || die "--grace needs a number"; GRACE="$2"; shift 2 ;;
    --tree)     [ "$#" -ge 2 ] || die "--tree needs a pid"; ROOT_PID="$2"; shift 2 ;;
    --tree-self) TREE_SELF=1; shift ;;
    --no-kill)  NO_KILL=1; shift ;;
    --kernel)   DO_KERNEL=1; shift ;;
    --json)     DO_JSON=1; shift ;;
    --quiet|-q) DO_QUIET=1; shift ;;
    --strict)   DO_STRICT=1; shift ;;
    --label)    [ "$#" -ge 2 ] || die "--label needs a name"; LABEL="$2"; shift 2 ;;
    --selftest) DO_SELFTEST=1; shift ;;
    --help|-h)  usage; exit 0 ;;
    --)         shift; while [ "$#" -gt 0 ]; do CMD+=("$1"); shift; done ;;
    -*)         die "unknown option: $1 (see --help)" ;;
    *)          CMD+=("$1"); shift ;;
  esac
done

if [ "$DO_SELFTEST" -eq 1 ]; then do_selftest; exit $?; fi

if [ "${#CMD[@]}" -gt 0 ]; then do_wrap "${CMD[@]}"; exit $?; fi

if [ -z "$ROOT_PID" ]; then
  if [ "$TREE_SELF" -eq 1 ]; then ROOT_PID=$$; else ROOT_PID=$PPID; fi
fi
do_report "$ROOT_PID"
if [ "$DO_STRICT" -eq 1 ] && [ "$VERDICT" = DANGER ]; then exit 2; fi
exit 0

# Worker rules - standing constraints for every card in this repo

Read this whole file before starting. Card briefs reference it instead of restating it.

## Build and toolchain
- Work in formal/. lake build must run in formal/, never the repo root.
- ALWAYS finish with lake build. lake env lean does NOT apply the package autoImplicit=false lakefile
  option AND it reads stale oleans for sibling modules you just edited, so a file can pass under
  lake env lean and FAIL lake build.
- Plain lake build only. NEVER ram_guard --limit 6G: it is KILLED at 11.8 GiB and leaves .olean files
  missing, which produces FALSE register reds.
- A fresh worktree should be made with formal/scripts/newbox.sh, which APFS-clones the warm .lake
  (~30 s, 9842 oleans) so the build is incremental (~2 min) instead of a 30-55 min cold build.
- Scripts live in formal/scripts/, not the repo root.
- The read tool returns at most ~2000 lines by default. Never assume a read returned the whole file.
  WIP-commit before any large rewrite; a truncated write-back once destroyed 3400 lines.
- timeout is absent on this box. Background long runs and read the log.
- A /-! doc block closes with -/ , not with */ .

## Gates you must print, never infer
- verify.sh --quick exit 0. NEVER run full checks.sh or verify.sh (rule W9).
- assert_axioms Midfall.LoweringV3.lowering_correct with native [] must print ok (4 named, 0 native),
  and the same for lowering_sound. It checks the ROOT, not each cone, so watch for Classical.choice
  creeping into a cone via simp or decide.
- KAT: python3 scripts/kat_gate.py takes 17-28 min and needs ELAN_HOME set to HOME/.elan and
  HOME/.elan/bin on PATH. It also asserts the object fingerprint. If it will not fit your budget, SAY
  SO rather than reporting an inferred pass. Four cards have correctly claimed neither way.
- Do NOT run gen_sorry.sh; the orchestrator regenerates the register at merge time. Report your own
  sorry delta with python3 scripts/lean_grep.py sorry FILE.
- Never hand-edit SORRY.md.
- Baseline: register 85 data rows / 18 ROOT (a main-tree reading of 86 is stale oleans, not a
  contradiction); cones lowering_correct 18, lowering_sound 8; fingerprint 14,109 tokens /
  0x3149ae4f...bef176; KAT 1633/118.

## Hard bounds
- D-P71: theorems are generic in the render, program, context and template table. No fixture in a
  statement. native_decide only in Midfall/Instances/, never inside a reported cone.
- NEVER add a hypothesis to ValidV3, ValidW, a row, a bundle or the root. If a fact is missing, STOP,
  record a PG_* row with the exact goal state, and report it. A hypothesis on an ARM LEMMA is fine.
- NO FROZEN FILE: Midfall/Statements.lean and LoweringV2 Program.lean, Shared.lean, Statements.lean
  (three entries in Frozen.sha256). No re-hash is authorised for a worker.
- No v1 .lean. vendor/ is READ-ONLY. Midfall/Generator/Quotient/VmReference.lean is READ-ONLY.
- W12: every new sorried statement needs a PROVED falsifier. W13: no refuted hole.
- At most 60 s per tactic call. NEVER raise maxHeartbeats or maxRecDepth.
- New files must be added to formal/Midfall.lean or check_orphans.py fails, and that check is NOT in
  verify.sh --quick.

## Git discipline
- Add ONLY your own files by explicit path. NEVER git add -A or git add . - it has twice swept another
  agent uncommitted work into a commit and left a HEAD that did not compile.
- Never git checkout --, git restore or git reset --hard on uncommitted work.
- WIP-commit every 45 min. Never push your branch. Never touch formal/baseline or /Users/julian/midfall,
  which is the merge tree.
- Verify your own base commit and branch and report them.

## Lean surface facts already paid for
- decide AND omega both hit maxRecDepth on any goal OR hypothesis containing 2^256 or a Nat.mod by it.
  Keep such facts as named theorems (frModulusWord_toNat, BitVec.isLt frModulusWord).
- abel, ring and omega are available through the existing Mathlib import chain; no new import needed.
  Use abel/ring instead of add_assoc juggling.
- simp only [List.find?, h] DOES NOT WORK and puts Classical.choice in the cone. Use find?_head and
  selectSwitch_head (case list as an explicit argument), both proved with no axioms.
- Step.argsCons takes (rest-derivation, head-derivation), and evaluates the REST before its head
  (BigStep.lean:209-212), so memory touch order is NOT source order.
- Step.assignVal needs (vars := [...]) plus (by rfl). Step.lit needs Dialect.Value fully specified
  because Dialect.litValue is not invertible; pass (l := Literal.number n). A let or have bound state
  argument breaks it; qlit is the fix.
- SyntaxEq.stmtsBeq does NOT kernel-reduce (WellFounded.fix), so decide and rfl on it fail.
- rw rewrites only the FIRST match instantiation; use simp only for equation lemmas occurring twice.
  rw [if_pos] fails on a Decidable-instance mismatch; use split at h.
- cases h : rec.field does NOT substitute; destructure the record first. List.Nodup must be
  destructured with cases hnod with | cons because it is Pairwise neq, so hnod.2 is invalid.
- The equation form | cons a as ih fails: as is a keyword.
- BitVec.eq_of_toNat_eq, not BitVec.toNat_inj. List.find? unfolds to match decide (y = x), so use
  decide_eq_false. if_pos and if_neg are deprecated for ite_eq_left and ite_eq_right.
- Bool.eq_true_or_eq_false does not exist; use cases h : b with | true | false.
- These DO NOT EXIST: List.mem_zip, List.getD_map, List.sum_mul, List.zipWith_eq_map_zip,
  List.get?_map, List.get?_zip, List.get_range', List.get?_eq_get, List.mem_iff_get?,
  List.get?_range, List.nodup_iff_get?_eq_get?, Array.get?_toList (real name
  Array.getElem?_toList), ZMod.val_inj, Prod.fst_mk, List.map_eq_map_of_mem, List.congr, List.map_congr,
  List.get?, List.eq_of_getEq, List.get_map. Several local replacements are already proved in
  QvmFold, QvmFoldLin, QuotientFrame and QuotientArms - grep before writing a new one.
- These DO exist: List.length_map, List.length_replicate, List.replicate_succ, List.mem_reverse,
  List.cons.injEq, Option.some.inj, Array.getElem?_eq_getElem.
- norm_num refuses 2^280 and 2^336. omega dies on 2^256.
- data is reserved for BINDERS where YulSemantics.Syntax is reachable; write
  { ev with <<data>> := ... } for field updates.
- #cone_sorries needs import Midfall.Tools.ConeSorries.

## Metric honesty
- cone_sorries counts proof-term dependencies. A row whose proof is a bare sorry cites NOTHING, so
  closing its named leaves does NOT move the cone until the row proof cites them. Many cards move no
  cone and that is expected and fine.
- Report what you proved on its own terms. Do not restructure a row proof to manufacture a cone drop.
- Never write a claim a tool did not print, including your own wrapper exit codes.
- If you find a defect in the generated contract or the generator rather than in the Lean port, that is
  a standing request from the human: stop, land the counterexample, and report it loudly.

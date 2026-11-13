# P-BYTES - the `Array.foldl` lemma that unblocks the scalar half of the codec repair.

Status: READY. This has been on the queue for many rounds and **P-REPIN just made it
load-bearing**: the frozen `verifyNative_iff_msgs` is repaired on its G1 half, and its scalar
half needs `frOfRepr_frToRepr`, which is a registered `sorry` blocked on exactly these byte
lemmas.

## The chain

```
Common/Bytes.lean byte lemmas
  -> Assumptions/Codec.lean:169 frOfRepr_frToRepr   (registered sorry)
  -> the scalar half of the D-P27 codec repair
  -> verifyNative_iff_msgs becomes known-provable in BOTH halves
```

P-REPIN's audit finding 5 said this precisely: *"the amended statement is still not known
provable, and the reason is now precise rather than implied."* This package removes that reason.

## The blocker, as recorded

`Codec.lean:157-168` records that the proof needs **two byte lemmas** assigned to design1 M5-2.
The known obstacle from earlier rounds: **`Array.foldl` is not defeq to `List.foldl` in Lean
4.35, and core has no `Array.foldl_eq_foldl_data`**. So a proof by `induction`/`simp` over the
list spelling will not transfer to the array spelling that `Bytes` uses.

**Re-verify this before relying on it** - it is a claim from an earlier round, and briefs in
this project have been wrong repeatedly. Check what `Bytes.data` actually is, what fold
combinators are available, and whether a `Fin`-indexed or `List.ofFn` formulation sidesteps the
issue entirely.

## Deliverable

1. **`bytesToNatLE_natToBytesLE`** (or the correct pair of lemmas `Codec.lean` names) in
   `Midfall/Common/Bytes.lean`, with the width hypothesis `p <= 2^256` handled exactly as
   `Codec.lean:157-168` documents - it is **load-bearing for the encoder-first direction and
   deliberately absent from the decoder-first one**.
2. **Discharge `frOfRepr_frToRepr`** at `Codec.lean:169`, removing that registered `sorry`.
3. **Check the two KAT gates** that were blocked on it (`frOfRepr_frToRepr` and
   `feToU256_frToRepr` per the earlier note) and confirm they now have real content.
4. **Update `SORRY.md`** - the count should go **64 -> 63**. That is the first sorry *removal*
   in many rounds, so verify the register and the gate agree.

## Constraints

* **D-P23 both halves**: the new lemma needs a witness AND a falsifiability demonstration.
  In particular, show the width bound is **actually needed** - exhibit a `p > 2^256` case where
  the round trip fails, or state precisely why you cannot.
* **Do not edit `Statements.lean` or `Statements.sha256`.** The frozen file is protected by the
  gate added last package; a lemma elsewhere cannot change it.
* **`check_frozen_axioms.py` will react** if a frozen statement's axiom set changes - that is
  expected and correct. If it reddens, investigate; do not adjust the gate.
* **RAM (D-P31)**: state an expected peak before VM work and run under `ram_guard.sh`. Use
  `--proc-limit 6G --limit 24G` for builds - a naive tree budget **kills a legitimate cold
  build**, which last package demonstrated by accident at 10.62 GiB.
* Do NOT edit Rust or `vendor/`. Do NOT git add or commit.
* Verify existence with `#check`, not grep piped through `head`. **Never perturb the working
  tree in place.** Numbers from `lake build` and `scripts/checks.sh` only.
* **`checks.sh` hazard**: anchored edits have broken it repeatedly. Assert anchor uniqueness,
  `bash -n`, full run, occurrence count.

## Environment

Repo `/Users/julian/midfall`, branch `formal/baseline`, tag `formal-baseline-v1` at `df7e607`.
Build green at **5155 jobs**, 109 modules; `checks.sh` green, 13 sections: **64 tracked
sorries**, 1286 KATs across 85 files, **158 statement fragments**, 12 fact families, 8 + 23
bundles, 30 baseline pins, Statements hash `40d97dc7…dc6e` OK.

Read first: `Midfall/Common/Bytes.lean` (lines 40-120 - the definitions and existing KATs),
`Midfall/Assumptions/Codec.lean:140-180` (the blocker note and the gated sorry),
`docs/plans/P-SE-evidence/design1.md` M5-2 (the assigned lemmas), `docs/design.md` D-P27.

## Acceptance

- `lake build` and `bash scripts/checks.sh` green; **tracked sorries 63**.
- `frOfRepr_frToRepr` proved, with the width bound's necessity demonstrated.
- **Required finding**: with the scalar half closed, is `verifyNative_iff_msgs` now **known
  provable** in both halves - i.e. does any remaining sorry block it? If yes, name it.

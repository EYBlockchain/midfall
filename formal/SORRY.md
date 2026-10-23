# sorry register

Every `sorry` in `formal/` is listed here with an owner and the work package
that removes it. CI (`.github/workflows/formal.yml`) fails if a `sorry`
appears that is not listed, or if a listed one disappears without this file being
updated.

A bare `sorry` outside this register is never allowed; a missing proof becomes a
named hypothesis structure in `Midfall/Assumptions/` instead (plan Section 3,
gap policy).

| file | decl | owner | removed by |
|---|---|---|---|
| (none yet) | | | |

## Upstream sorries we would depend on

From `docs/ecosystem.md`: ArkLib admits 112 proof `sorry`s. None of them may
appear in the `#print axioms` closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* `ArkLib/AGM/Basic.lean:189` `AGM.Adversary.run` - we write our own AGM.
* `ArkLib/OracleReduction/FiatShamir/Basic.lean:173` `fiatShamir_completeness`
  - we prove the FS step ourselves (S4).
* `Security/Implications.lean:49` and `:189`, all `liftContext_*`, all
  `append_*` - S2 must not route through these.

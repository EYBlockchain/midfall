# sorry register

Every `sorry` in `formal/` is listed here with the work package that removes
it. CI (formal/scripts/checks.sh, run by .github/workflows/formal.yml) fails if a
`sorry` appears that is not listed here, or if a listed one disappears without this
file being updated.

A bare `sorry` outside this register is never allowed; a missing proof becomes a
named hypothesis structure in `Midfall/Assumptions/` instead (plan Section 3, gap
policy). The Phase 1 exit criterion is explicitly `Statements.lean compiles with
sorry`, so what is listed here is the planned Phase 1 state, not sloppiness.

| file | line | declaration | removed by |
| Midfall/Halo2/Exec/Native.lean | 42 | `TranscriptM (DualMSM (Fr p) G₁ G₂ Gₜ) := sor` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 61 | `Option (List (Msg (Fr p) G₁)) := sorry` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 66 | `Except Fault (DualMSM (Fr p) G₁ G₂ Gₜ) := so` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 71 | `Except Fault Unit := sorry` | Phase 2 (L0 port) |
| Midfall/Halo2/Spec/Piop.lean | 26 | `(ms : List (Msg (Fr p) G₁)) : Prop := sorry` | Phase 4 (spec layer) |
| Midfall/Halo2/Spec/Relation.lean | 32 | `def CircuitIndex.usable (idx : CircuitIndex ` | Phase 4 (spec layer) |
| Midfall/Halo2/Spec/Relation.lean | 40 | `(e : Expression (Fr p)) (i : Nat) : Fr p := ` | Phase 4 (spec layer) |
| Midfall/Halo2/Spec/Relation.lean | 44 | `(c : Cell) : Fr p := sorry` | Phase 4 (spec layer) |
| Midfall/Halo2/Spec/Relation.lean | 51 | `(exprs : Array (Expression (Fr p))) (i : Nat` | Phase 4 (spec layer) |
| Midfall/Statements.lean | 45 | `verifyMsgs keccak256 F params vk inst ms = .` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 57 | `Spec.accepts H F params vk inst ms := by sor` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 72 | `verifyMsgs keccak256 Features.solidity param` | frozen statements (S1..S7 land later) |

## Upstream sorries we must not depend on

From docs/ecosystem.md: ArkLib admits 112 proof sorries. None of them may
appear in the #print axioms closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* ArkLib/AGM/Basic.lean:189 AGM.Adversary.run - we write our own AGM.
* ArkLib/OracleReduction/FiatShamir/Basic.lean:173 fiatShamir_completeness -
  we prove the FS step ourselves (S4).
* Security/Implications.lean:49 and :189, all liftContext_*, all append_* -
  S2 must not route through these.

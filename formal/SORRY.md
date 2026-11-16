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
| Midfall/Halo2/Spec/Piop.lean | 67 | `(ms : List (Msg (Fr p) G₁)) : Prop := sorry` | Phase 4 (spec layer) |
| Midfall/Lowering/AccEncoding.lean | 194 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/AccEncoding.lean | 254 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/AccEncoding.lean | 306 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Accumulator.lean | 142 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Accumulator.lean | 955 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Calldata.lean | 743 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Calldata.lean | 795 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Calldata.lean | 1288 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Obligations.lean | 771 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Obligations.lean | 806 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 540 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 574 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 597 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 620 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 648 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 697 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 748 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 791 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 851 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 1330 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Partials.lean | 1344 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Qvm.lean | 631 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Qvm.lean | 698 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Qvm.lean | 713 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Qvm.lean | 768 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Qvm.lean | 995 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/QvmFold.lean | 338 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/QvmFold.lean | 376 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/QvmFold.lean | 434 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Snapshot.lean | 387 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/Surface.lean | 718 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Lowering/VkDigest.lean | 72 | `sorry` | P-SE: semantic equivalence obligations |
| Midfall/Statements.lean | 95 | `Spec.accepts E H F params vk inst ms := by s` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 123 | `verifyMsgs (Gₜ := Gₜ) E keccak256 Features.s` | frozen statements (S1..S7 land later) |
| Midfall/Yul/Bridge.lean | 186 | `sorry` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall/Yul/Bridge.lean | 335 | `sorry` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall/Yul/Bridge.lean | 342 | `sorry` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall/Yul/Bridge.lean | 872 | `sorry` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |
| Midfall/Yul/Bridge.lean | 1086 | `sorry` | P-SE stage 1-2: Yul run/contracts layer (semantic equivalence) |

## Upstream sorries we must not depend on

From docs/ecosystem.md: ArkLib admits 112 proof sorries. None of them may
appear in the #print axioms closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* ArkLib/AGM/Basic.lean:189 AGM.Adversary.run - we write our own AGM.
* ArkLib/OracleReduction/FiatShamir/Basic.lean:173 fiatShamir_completeness -
  we prove the FS step ourselves (S4).
* Security/Implications.lean:49 and :189, all liftContext_*, all append_* -
  S2 must not route through these.

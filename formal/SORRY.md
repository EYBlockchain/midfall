# sorry register

Every `sorry` in `formal/` is listed here with the work package that removes
it. CI (.github/workflows/formal.yml) fails if a `sorry` appears that is not listed
here, or if a listed one disappears without this file being updated.

A bare `sorry` outside this register is never allowed; a missing proof becomes a
named hypothesis structure in `Midfall/Assumptions/` instead (plan Section 3, gap
policy). The Phase 1 exit criterion is explicitly `Statements.lean compiles with
sorry`, so what is listed here is the planned Phase 1 state, not sloppiness.

| file | line | declaration | removed by |
|---|---|---|---|
| Midfall/Common/Codec.lean | 29 | `G1OfCompressed` | Phase 1 curve instance |
| Midfall/Common/Codec.lean | 33 | `E1OfEip` | Phase 1 curve instance |
| Midfall/Common/Codec.lean | 41 | `G1OfEip` | Phase 1 curve instance |
| Midfall/Halo2/Exec/Native.lean | 42 | `DualMSM.check` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 50 | `TranscriptM (DualMSM (Fr p) G₁ G₂) := so` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 64 | `Option (List (Msg (Fr p) G₁)) := sorry` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 69 | `Except Fault (DualMSM (Fr p) G₁ G₂) := s` | Phase 2 (L0 port) |
| Midfall/Halo2/Exec/Native.lean | 74 | `Except Fault Unit := sorry` | Phase 2 (L0 port) |
| Midfall/Halo2/Spec/Piop.lean | 26 | `(ms : List (Msg (Fr p) G₁)) : Prop := so` | Phase 4 (spec layer) |
| Midfall/Statements.lean | 42 | `verifyMsgs keccak256 F params vk inst ms` | frozen statements (S1..S7 land later) |
| Midfall/Statements.lean | 54 | `Spec.accepts H F params vk inst ms := by` | frozen statements (S1..S7 land later) |

## Upstream sorries we must not depend on

From docs/ecosystem.md: ArkLib admits 112 proof sorries. None of them may
appear in the #print axioms closure of a Midfall theorem unless it is listed
here as an explicit assumption. The known hazards are:

* ArkLib/AGM/Basic.lean:189 AGM.Adversary.run - we write our own AGM.
* ArkLib/OracleReduction/FiatShamir/Basic.lean:173 fiatShamir_completeness -
  we prove the FS step ourselves (S4).
* Security/Implications.lean:49 and :189, all liftContext_*, all append_* -
  S2 must not route through these.

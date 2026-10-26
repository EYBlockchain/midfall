# P-13 - templates to Lean (the block with no Rust counterpart to diff against)

Status: DRAFT. Blocked on P-05..P-12 (the emitters need Data, Ptr, Value, the plan
types, the QVM program). This is the block PLAN 14.7 names as the widest error bar, and
the reason is structural, not size.

## The finding that shapes this package

`proofs/solidity-verifier/templates/` is 4,324 lines across 15 files, and they are not
one kind of thing:

| kind | files | lines | comparable under D-P13? |
|---|---|---:|---|
| Yul partials | `partials/verifier/{AssemblyHelpers,TranscriptProofParser,AccumulatorHelpers,Lagrange,Pcs,FinalPairing,VkLoading,QuotientAndLinearization,TraceReturn}.yul` + `partials/quotient_numerator/{QuotientHelpers,QuotientNumeratorBlock}.yul` | 3,363 | **yes** - `stmtsBeq` on the vendored AST |
| Solidity partials | `partials/verifier/{Constructors,Constants,PrecompileSmoke}.sol` | 539 | **no** - not Yul |
| Solidity contracts | `contracts/{Halo2Verifier,Halo2VerifyingKey,Halo2QuotientEvaluator}.sol` | 422 | **no** - not Yul |

PLAN 8 says one Lean fn per template/partial producing a `Yul.Block`, and M3's
acceptance is golden AST equality (formatting-insensitive, D-P13) on corpus + Moonlight.
**That is not achievable for the 961 lines of Solidity**, because a Solidity file is not
a Yul block. The design already knows this - PLAN 9.5's `Lowered` carries `headGuard`
and `main` as Yul blocks plus a separate `shell : SolShell` - but the acceptance
criterion does not say which comparison covers which half.

So the block has two obligations needing two different tripwires:

1. **Yul half:** port each `.yul` partial to a Lean fn returning `Block EVM.Op`, and
   golden-test with `YulSemantics.SyntaxEq.stmtsBeq` against the embedded assembly of
   the tracked dump. This is the D-P13 relation and the one the theorems will use.
2. **Solidity half:** the only available oracle is textual. `scripts/normalise_sol.py`
   already exists for this (comments and blank lines stripped, whitespace collapsed,
   bytes compared) and was measured to be *stricter* than `stmtsBeq`. Use it as the CI
   tripwire and state plainly that it is conformance evidence, not proof.

**Action for the orchestrator before this fires:** amend PLAN 11's M3 acceptance row to
say golden AST equality for the Yul partials and normalised-byte equality for the
Solidity shell, so the milestone is checkable rather than aspirational. That is a
wording change to an acceptance criterion, not a weakening of a theorem, but it should be
recorded rather than assumed.

## Hazards

1. **Askama control flow is not Lean control flow.** The templates use for/if/match
   blocks and the `hex` / `hex_padded` filters. Filters are already ported in
   `Filters.lean`; the loops must be ported as the same recursions the Rust unrolls, in
   the same order. A template iterating a HashMap would be nondeterministic - check
   every loop source for map iteration (P-05 established the reference sorts before the
   only whole-map iteration it has).
2. **Whitespace and comments are not free in the Solidity half.** `normalise_sol.py`
   strips them, which is why it can be the tripwire; but the emitted bytes still have to
   be valid Solidity, so a port that drops a newline inside a string literal changes the
   artifact without changing the AST. Gate the shell text, not only the AST.
3. **`QuotientNumeratorBlock.yul` is 1,442 lines in one file** - the largest template and
   the QVM's Yul. It cannot be ported before P-09d (yul_emit). Do not attempt it in the
   same package as the small partials.
4. **`FinalPairing.yul` (92 lines) is the target of the pulled-forward
   `finalPairing_spec`.** It is small, it is the first semantic-equivalence result, and
   PLAN 6 names its pairing-input layout (`[RHS|G2|LHS|NEG_S_G2]`, AssemblyHelpers.yul
   lines 213-232) as the thing the DualMSM reorder lemma must match. That argues for
   porting `AssemblyHelpers.yul` and `FinalPairing.yul` **first** in this block, out of
   template order, so `finalPairing_spec` is not blocked on the other 13.
5. **`PrecompileSmoke.sol` (216 lines) is a test-only render mode** (misc-fixes step 6).
   Decide explicitly whether it is in the supported profile; PLAN 9.5's
   `Supported.production` excludes trace and gas checkpoints but says nothing about the
   smoke render.

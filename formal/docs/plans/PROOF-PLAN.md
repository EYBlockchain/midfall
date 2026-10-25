# Proof plan - S1..S7 mapped onto ArkLib / VCVio and onto verified sources

Status: DRAFT, round 10. Written by the planner during build windows. This is the
document PLAN section 10 step 1 (`docs/security.tex`) should be written against: every
security statement gets (a) the library theorem it instantiates, (b) the paper result
that theorem rests on, (c) the gap that is ours to close.

Everything below marked VERIFIED was checked against the pinned ArkLib/VCVio sources in
`formal/.lake/packages/` or against the IACR/arXiv page named. Everything marked
UNVERIFIED is a lead, not a citation - do not put it in `security.tex` as written.

## What the libraries actually give us

| capability | identifier | file:line | state |
|---|---|---|---|
| KZG perfect correctness | `KZG.CommitmentScheme.correctness` | `Correctness.lean:169` | VERIFIED - fully proved, no sorry |
| **KZG function binding** | `KZG.CommitmentScheme.function_binding` | `FunctionBinding/Basic.lean:635` | VERIFIED - proved under `Groups.arsdhAssumption` (ARSDH, cited by ArkLib as CGKY25 Def 9.6) |
| ARSDH assumption | `Groups.arsdhAssumption` | `HardnessAssumptions.lean:127` | VERIFIED - a `Prop`; the game itself (`arsdhExperiment:120`) is noncomputable |
| protocol shape | `ProtocolSpec` | `OracleReduction/ProtocolSpec/Basic.lean:31` | VERIFIED - `dir : Fin n -> Direction`, `Type : Fin n -> Type` |
| oracle reduction | `OracleReduction` | `OracleReduction/Basic.lean:663` | VERIFIED |
| knowledge soundness (named extractor) | `Verifier.knowledgeSoundnessWith` | `Security/Basic.lean:298` | VERIFIED - `def : Prop`, straight-line extractor in the statement |
| knowledge soundness (existential) | `Verifier.knowledgeSoundness` | `Security/Basic.lean:343` | VERIFIED; bridge lemmas `knowledgeSoundness_iff_exists_with:364`, `knowledgeSoundness_of_with:373` |
| **round-by-round KS** | `Verifier.rbrKnowledgeSoundness` | `Security/RoundByRound.lean:457` | VERIFIED - error is a function `pSpec.ChallengeIdx -> R>=0`, which is exactly the shape PLAN 9.4's `roundErr` wants |
| rbr KS implies KS | `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` | `Security/Implications.lean:189` | **SORRY at :194** - unusable |
| KS implies soundness | `Verifier.knowledgeSoundness_implies_soundness` | `Security/Implications.lean:49` | **SORRY at :63** - unusable |
| sequential composition glue | `append_{soundness,knowledgeSoundness,rbr*}` | `Composition/Sequential/Append/Security.lean:49,60,81,96` | **all SORRY** - unusable |
| Fiat-Shamir prover/verifier | `Prover.fiatShamir` / `Verifier.fiatShamir` / `Reduction.fiatShamir` | `FiatShamir/Basic.lean:114,130,140` | VERIFIED - the transformation exists |
| Fiat-Shamir completeness | `fiatShamir_completeness` | `FiatShamir/Basic.lean:163` | **SORRY at :173** |
| **Fiat-Shamir soundness / KS** | - | - | **DOES NOT EXIST in ArkLib.** No `fiatShamir_soundness` or `fiatShamir_knowledgeSoundness` anywhere. This is the single biggest structural gap. |
| AGM adversary | `AGM.Adversary.run` | `AGM/Basic.lean:190` | **SORRY** - hence our own AGM, already decided |
| Plonk constraint system | `Plonk.ConstraintSystem` | `ProofSystem/ConstraintSystem/Plonk.lean` | VERIFIED but **wrong shape**: 3-wire `WireIndices a b c` + `Selector qL qR qO`. Halo2's arbitrary-`Expression` custom gates, logUp and trash do not fit it. |
| Plonk protocol | `ProofSystem/Plonk/Basic.lean` | 46 lines, nothing imports it | **stub** - no protocol, no KS theorem to reuse |
| random oracle | `OracleSpec.randomOracle` | VCVio `RandomOracle/Basic.lean:24` | VERIFIED - lazy, with caching law `run_eq:43` |
| logging oracle | `OracleSpec.loggingOracle` | VCVio `LoggingOracle/Core.lean:311` | VERIFIED - `loggingOracle.fst_map_run_simulateQ:318` proves logging does not change behaviour |
| query log / simulation | `QueryLog:382`, `simulateQ:30` | VCVio `Structures.lean`, `SimulateQ.lean` | VERIFIED |
| probability notation | `Pr{ doSeq }[ event ]` | VCVio `ProbabilityNotation.lean:39,63` | VERIFIED - **there is no bare `Pr[...]` form**, so PLAN 9.4's notation is not Lean |

## The three conclusions that follow

1. **S3 is largely a freebie, S4 is not.** ArkLib already proves KZG function binding
   under ARSDH, so the multi-open binding statement can be *instantiated* rather than
   proved - but there is no Fiat-Shamir soundness theorem anywhere in ArkLib, so the
   step that turns an interactive-protocol statement into the noninteractive verifier is
   entirely ours. PLAN 9.4's S4 is therefore not a supporting lemma, it is the critical
   path of the whole security track.
2. **Do not route through rbr-to-KS.** `rbrKnowledgeSoundness_implies_knowledgeSoundness`
   is `sorry`, so S2 (which states rbrKS) cannot be used to derive S1 (which states KS)
   by invoking ArkLib's bridge. Either prove the bridge for our single protocol or
   instantiate `knowledgeSoundnessWith` directly and keep rbr as an intermediate we
   discharge ourselves. This is the same trap R-31 recorded for our own code, in a
   dependency.
3. **ArkLib's Plonk is not our protocol.** The 3-wire selector shape cannot express a
   Halo2 `Expression` tree, so `Spec/Relation` and `Spec/Piop` stay ours. What we can
   reuse is the generic layer: `ProtocolSpec` for the round structure, `OracleReduction`
   for the reduction, `Verifier.knowledgeSoundnessWith` for the statement, and VCVio for
   the oracle semantics and the probability monad.

## Per-statement mapping

| stmt | what it claims | library target | paper source | ours to prove |
|---|---|---|---|---|
| S1 `halo2_knowledgeSound` | noninteractive verifier is KS in AGM+ROM, reduces to q-DLOG | `Verifier.knowledgeSoundnessWith` (`Security/Basic.lean:298`) | PLONK (Gabizon-Williamson-Ciobotaru) Thm 1 for the gate/permutation core; logUp via ePrint 2022/1530 | the whole reduction: PIOP KS, FS soundness, KZG binding, AGM extraction, and the error budget |
| S2 `halo2PIOP_rbrKS` | the interactive PIOP is round-by-round KS | `Verifier.rbrKnowledgeSoundness` (`RoundByRound.lean:457`) - error is `ChallengeIdx -> R>=0`, matching `roundErr` | PLONK section on the gate identity + permutation grand product; logUp rational identity from 2022/1530; **char bound: see 2024/2067 below** | per-round bad-point sets (already in `Spec/Degrees.lean`) and the nonzeroness open problem `op:nonzero` |
| S3 `kzgMultiOpen_binding` | accepted multi-open implies the opened polynomials evaluate as claimed | **`KZG.CommitmentScheme.function_binding`** (`FunctionBinding/Basic.lean:635`) under ARSDH | ArkLib's own chain (`reduction:118`, `mapFunctionBindingToArsdh:100`, `functionBindingGameExt:157`, `arsdh_error_bound:623`); KZG (Kate-Zagrosky-Goldberg) for the scheme | the *bridge*: showing our ported `multi_prepare` + `DualMSM.check` computes exactly ArkLib's binding predicate. Not free - the point-set ordering and the x1..x4 schedule must be shown to agree |
| S4 `keccakChain_simulates_fs` | the Keccak sponge transcript simulates ArkLib's FS oracle | none exists | PLONK's Fiat-Shamir treatment; the generic FS soundness argument | **entirely ours.** Includes the reseed rule (`digest` becomes the next state) and `digest mod r` reduction, both already pinned by KATs after R-20 |
| S5 `alpha_batching_sound` | batching two pairing checks with a transcript-derived alpha is sound | none | Halo (Boneh-Droran-Ghosh-Lauter) for the accumulator idea; the root-count is elementary | the `atMostOneRoot` lemma needs the two checks not both failing - `batched_complete` and `batched_atMostOneRoot` in PLAN 9.4 - and the lazy-sampling commit-before step |
| S6 `halo2_complete` | honest prover is accepted with high probability | `KZG.CommitmentScheme.correctness` (proved) + our own completeness | PLONK + logUp completeness | the honest-prover spec (`honestProve`) does not exist yet; PLAN section 1 puts prover code out of scope, so this is a *mathematical* spec only |
| S7 `contract_knowledgeSound` | the deployed contract is KS | derived: S1 + S5 + `lowering_equivalence` + lazy sampling | - | depends on M7/M8 being done; nothing to start yet |

## D-P14: the truncated batching coefficients - what is actually needed

The gap, precisely: under `truncated-challenges` the x1 and x4 batching coefficients are
`truncate(x^j)`, i.e. the low 128 bits of the canonical representative of `x^j mod r`,
re-embedded in `Fr`. The verifier's check is `sum_j T(x^j) * C_j = 0` where `T` is that
truncation map. `T` is not a field operation, so the left side is **not a polynomial in
x**, and Schwartz-Zippel - which is what every `roundErr` row currently rests on - does
not apply to it.

What we need is a bound on `|{ x in Fr : sum_j T(x^j) C_j = 0 }|` for a fixed nonzero
vector `C`, where `C` is fixed before `x` is sampled (that ordering is what the AGM+ROM
game gives us and it is essential - without it the adversary picks `C` after seeing `x`
and wins trivially).

Leads, none yet verified against a primary source:

- The truncation image has `2^128` elements, so a naive union bound over "the j-th
  coefficient is wrong" gives nothing; the structure is in the *joint* distribution of
  `(T(x), T(x^2), ..., T(x^d))` as `x` ranges over `Fr`.
- This smells like the number-theoretic literature on the distribution of bits of powers
  in finite fields (exponential-sum methods). **UNVERIFIED - I could not confirm a
  specific reference through the search interfaces available this session** (the web
  search engine was failing and arXiv full-text returned nothing for the phrases I
  tried). Do not cite anything here until someone pulls the actual paper.
- A cheaper route worth checking first: if the truncation is only used to *shorten*
  challenges, one can instead prove soundness of the untruncated batching equation and
  then argue the truncated check is implied by it, or is implied with the exception of a
  bounded set of `x`. Whether that implication holds depends on `T` being injective on
  the relevant range, which it is not (`T` has a `2^128`-sized image inside a `~2^255`
  field). Flagged as the first thing to think about, not as a plan.
- **Do not** solve this by changing the deployment: D-P14 fixes truncation in the
  supported profile for output compatibility.

## Bibliography corrections for docs/security.tex

Two entries in the current `\begin{thebibliography}` are wrong, both found by checking
the primary source rather than recalling it:

1. `plookup` is given as "Sub-linear Polynomial Commitment Scheme and its Application to
   Lookup Tables". The actual paper at ePrint 2020/315 is **"plookup: A simplified
   polynomial protocol for lookup tables", Ariel Gabizon and Zachary J. Williamson**.
2. `logup` is given as "GroBbaek, Hansson, Triandopoulos et al. LogUp: for combining
   lookup arguments. 2022". No such paper is findable on ePrint by title. The formal
   reference for the logarithmic-derivative lookup argument is **Ulrich Habock,
   "Multivariate lookups based on logarithmic derivatives", ePrint 2022/1530** - and
   2024/2067 cites it as "[eprint 2022/1530]" for logUp, which confirms the chain.
3. Add: **Eagen and Habock, "Bypassing the characteristic bound in logUp", ePrint
   2024/2067** - directly relevant to PLAN section 6's "logUp rational identity (char >
   n)", which is a hypothesis we currently carry. Their construction abstracts pole
   multiplicity to remove the bound. Whether it applies to the trash/logUp variant this
   codebase implements is an open question worth a look before we formalise the bound.
4. Also on file: Papini and Habock, ePrint 2023/1284 (GKR-variant of logUp) and Soukhanov,
   ePrint 2025/946 (LogUp*, small-table indexed lookups). Neither matches this codebase's
   argument shape as far as I have checked; recorded so the next reader does not re-find
   them.

## Verification pass (round 10) - what checking the sources actually changed

Every library claim above was re-opened in `.lake/packages/` rather than trusted from the
Phase 1 inventory, and every Rust claim re-read from source. Six library claims confirmed
exactly (`function_binding` proved with no sorry in its file; `rbrKnowledgeSoundness`
having error type `pSpec.ChallengeIdx -> R>=0`; the rbr-implies-KS bridge ending in
`by sorry`; **zero** hits for any `fiatShamir_soundness` / `fiatShamir_knowledgeSoundness`
in the whole ArkLib tree; `knowledgeSoundnessWith` at Security/Basic.lean:298;
`AGM.Adversary.run := sorry`). Four things in this plan or in R-22 were wrong or
incomplete:

1. **`truncate` is `pub(crate)`, not `pub fn`** - arithmetic.rs:247-252. Substance
   confirmed: `nb_bytes = NUM_BITS.div_ceil(8).div_ceil(2)` = 16 for Fr (255 bits), it
   takes the low 16 bytes of the canonical LE repr, reads them LE as a BigUint and
   re-embeds via `from_str_vartime`. Since 2^128 < r the embedding is exact, so
   `T : Fr -> Fr` is a genuine function with image exactly `[0, 2^128)`: **|im T| =
   2^128**, which is the quantity any bound must use. The `.unwrap()` at :251 is an R4
   site (unreachable: a decimal rendering of a BigUint always parses - argue it at the
   site, do not assume it).
2. **Five call sites, not two**: kzg/mod.rs:240, :301, :394, :502, :521 (this plan said
   393 and 501). All five are `#[cfg(feature = "truncated-challenges")]` with a
   `cfg(not(...))` alternate, so R8 requires both branches ported.
3. **x3 is also truncated** (kzg/mod.rs:287 and :457) - and that is *benign*, which is
   worth stating because it sharpens what D-P14 actually is. x3 is used as an evaluation
   *point*, not as a batching coefficient: the check is over `q_evals_on_x3` read from the
   proof. Sampling the point from a 2^128-sized subset instead of Fr changes only the
   denominator of a bad-point ratio, which is exactly what `chalMass` already models as
   `s / 2^128`. The x1/x4 rows fail for a different and harder reason: there the
   *coefficients* are `T(x^j)`, so the batched expression is not a polynomial in the
   sampled variable at all and no degree bound exists. **D-P14's scope is truncation of
   powers of the same challenge, not truncation per se.**
4. **`MSMKZG::collapse` is applied only under truncated-challenges** (kzg/mod.rs:502-503,
   `coms.iter_mut().skip(1).for_each(MSMKZG::collapse)`). I flagged this as potentially
   fatal to `lowering_equivalence` and then checked it: **it is mathematically inert.**
   `collapse` sets `scalars = [ONE]`, `bases = [self.eval()]`, and `eval` (msm.rs:140)
   reads only `scalars` and `bases` - never `labels`. So the collapsed MSM denotes the
   same group element and the pairing check is unchanged. What collapse destroys is the
   label metadata, and the code says so (msm.rs:90-92: NoLabel and Advice "are not
   relevant for the `verifier_gadget` in `midnight-circuits` (at least for now). Other
   types of labels may carry information that we do not want to lose"). The guard for
   that is a `debug_assert!`, so in the release reference profile it does not fire - a
   **diagnostic-integrity** issue, not a soundness one. Recorded at this, lower, altitude
   because the port still has to model the shape change (a 1-term MSM with scalar ONE is
   what the emitter sees), and because a reviewer who reads the earlier version of this
   bullet should see it was downgraded on evidence, not quietly dropped.
5. **What the generator itself does under the feature** (models.rs:606-614, field
   `truncated_challenges`, "driven by `cfg!(feature = "truncated-challenges")` in
   `SolidityGenerator::generate_verifier`"): it documents that **x3 is masked to 128 bits
   immediately after squeeze** and **x1/x4 powers are masked to 128 bits at use, with the
   internal full-precision accumulator preserved**. Two consequences for P-07 and for the
   lowering proofs. (a) The mask is applied *at use*, not to the stored power, so the
   Lean port must model a full-precision accumulator with a per-use truncation - getting
   this wrong changes nothing mathematically but changes the emitted Yul, and the golden
   test is the only thing that would notice. (b) The Default render model sets
   `truncated_challenges: false` (models.rs:1289), so any gate that renders from the
   default is testing the non-deployed profile. That is the same trap as R-36's stale
   artifact, one level down.

## Open checks this plan still owes

- ~~Does the generator apply the same collapse under the feature?~~ Answered: collapse is
  value-preserving (msm.rs:140 ignores labels), so the generator need not mirror it; the
  port must still model the shape change. See verification item 4.
- `function_binding` carries hypotheses `hp : p >= n + 2`, `hpair : pairing g1 g2 <> 0`,
  `[SampleableType G1]`. Our instantiation must discharge all three; `hpair` is exactly
  the non-degeneracy we hold as a named assumption in `Assumptions/Pairing.lean`, so S3
  inherits that assumption explicitly and the axiom audit must show it.
- PLAN 9.4 writes `Pr[= true | ...]`; VCVio's only form is `Pr{ doSeq }[ term ]`
  (ProbabilityNotation.lean:63, with `prEvent` noncomputable at :39). The frozen
  statements use the plan's notation as pseudo-Lean, which is allowed, but the real
  theorem must use the brace form - worth noting before someone tries to typecheck the
  plan text.

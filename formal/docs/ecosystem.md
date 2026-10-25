# Lean 4 Ecosystem Inventory (Phase 1)

Survey date: 2026-10-23. Method: `git clone --depth 50` (+ `git fetch --depth 50 origin <rev>` for
exact revs) into `/Users/julian/midfall/.cache/ecosystem/`, then source-level grep. **Nothing was
built**; no `lake update`, no executed `#print axioms`. Every `file:line` below was read from a
file. Anything not seen in a file is written "not found".

Clone roots (all paths below are relative to these):

| repo | URL actually used | HEAD / rev | local dir |
|---|---|---|---|
| ArkLib | `https://github.com/Verified-zkEVM/ArkLib` | `d023c5d31d7611ad772588b2da3286a7f3f0628b` | `.cache/ecosystem/arklib` |
| VCVio | `https://github.com/Verified-zkEVM/VCVio` | `88efe9715a9fa9e7d89635c38cf70259836766c2` | `.cache/ecosystem/vcvio` |
| CompPoly | `https://github.com/Verified-zkEVM/CompPoly` | `06686e4c70939af82203af21516f8ab8a21a8051` | `.cache/ecosystem/comppoly` |
| yul-semantics | `https://github.com/powdr-labs/yul-semantics` | `c9914c13df47efe026376723acd632bc33bc16e3` | `.cache/ecosystem/yul` |

> **Correction to the task brief:** `https://github.com/arkworks-rs/ArkLib` **does not exist**
> (GitHub API returns 404 for `arkworks-rs/ArkLib`, `arkworks-rs/arklib`, `VCio-labs/arkworks`).
> The authoritative ArkLib home is the **Verified-zkEVM** org, which also owns VCVio and CompPoly.

## 0. Toolchains and pins

| library | lean-toolchain | direct deps (source of truth) | mathlib rev |
|---|---|---|---|
| ArkLib | `leanprover/lean4:v4.35.0` (`lean-toolchain`) | `lakefile.toml`: VCVio rev `v4.35.0`, CompPoly rev `v4.35.0`, doc-gen4 `v4.35.0`, checkdecls `lean4.18.0` | not pinned in ArkLib's lakefile; `lake-manifest.json` resolves `mathlib = 56a005855ea17e0b0958f73ec801ae140b0a1679` |
| VCVio | `leanprover/lean4:v4.35.0` | `lakefile.lean:77`: require leanprover-community/mathlib @ git `v4.35.0`; also PolyFun (`lakefile.lean:73`); manifest: mathlib `56a0058...`, cslib `5b56df9...`, batteries `66e4691...`, aesop `4a174c4...` | `56a0058...` |
| CompPoly | `leanprover/lean4:v4.35.0` | `lakefile.lean`: mathlib @ git `v4.35.0`; `preferReleaseBuild := true` (prebuilt olean tarballs), `fixedToolchain := true` | `56a0058...` |
| yul-semantics | `leanprover/lean4:v4.33.0` | `lakefile.toml`: **Batteries only** (leanprover-community/batteries rev `v4.33.0`), and only for the lint driver -- "No library module imports it" | none (Mathlib-free) |

**Toolchain conflict:** ArkLib/VCVio/CompPoly = **v4.35.0**, yul-semantics = **v4.33.0**. A single
project cannot depend on both without either bumping yul-semantics or pinning to 4.33.0 (ArkLib
HEAD is literally titled "upgrade Lean and dependencies to v4.35.0", PR #1329).

## 1. ArkLib -- BLS12-381

**Headline: ArkLib contains no BLS12-381 at all.** A case-insensitive grep for `bls` over the whole
repo (`*.lean`, `*.md`, `*.toml`, blueprint) returns **zero hits**. The only curve file is
BN254. The BLS12-381 *scalar field* lives in CompPoly.

### 1a. What exists for BLS12-381 (in CompPoly, ArkLib's pinned dep)

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| scalar field size r | `BLS12_381.scalarFieldSize` | `CompPoly/Fields/BLS12_381/Basic.lean:22` | yes (`def`, `@[reducible]`) | `0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`; docstring: "255-bit, 2-adicity 32" |
| scalar field | `BLS12_381.ScalarField` | `CompPoly/Fields/BLS12_381/Basic.lean:25` | yes (`abbrev ... := ZMod scalarFieldSize`) | primality proved by Pratt certificate |
| primality proof | `BLS12_381.ScalarField_is_prime` | `.../Basic.lean:27` | proof (`theorem`) | uses `PrattCertificate'` -- no `native_decide` |
| Fact / Field instances | `instance : Fact (Nat.Prime scalarFieldSize)` / `instance : Field ScalarField` | `.../Basic.lean:47`, `:49` | yes | via `ZMod.instField` |
| fast Montgomery scalar field | `BLS12_381.Fast.ScalarField` | `CompPoly/Fields/BLS12_381/Fast.lean:52` | yes (`abbrev ... := FastField ...`) | `instMont64x8Field` `:38`; `ofField` `:56`; `ringEquiv : ScalarField ≃+* BLS12_381.ScalarField` `:61` |
| byte codec for Fr | `CompPoly.instByteCodecZMod` | `CompPoly/Data/Bytes/CanonicalNat.lean:95` | yes | class `CompPoly.ByteCodec` at `CompPoly/Data/Bytes/Codec.lean:33` (`width`, `toBytes`, `ofBytes?`, law `ofBytes?_toBytes`) |
| base field Fq | **not found** | -- | -- | no `baseFieldSize` / `BaseField` for BLS12_381 anywhere |
| Fp2 | **not found** | -- | -- | only a *generic* binomial-extension machinery: `CompPoly.Fields.Extension.Arithmetic.ExtensionParams` (`CompPoly/Fields/Extension/Arithmetic.lean:49`) and `Ext` (`:88`), with `instance [ByteCodec F] : ByteCodec (Ext P)` (`Extension/Bytes.lean:37`). No BLS12-381 instantiation of it. |
| Fp12 | **not found** | -- | -- | same as above; no tower for BLS12-381 |
| G1 curve / point type | **not found** | -- | -- | no `BLS12_381.G1`, no `WeierstrassCurve` for BLS |
| G1 group / r-torsion / `Module Fr` instance | **not found** (concretely) | -- | -- | ArkLib abstracts this instead -- see section 2 (`PrimeOrderWith` + `Module (ZMod p) (Additive G₁)`) |
| G2 | **not found** | -- | -- | |
| GT | **not found** | -- | -- | |
| pairing function | **not found** | -- | -- | greps for `def pairing`, `structure ... Pairing`, `class ... Pairing` over `ArkLib/**` return 0 hits |
| point compression / encoding | **not found** | -- | -- | no curve-point codec; only field codecs + generic `Serialize`/`DeserializeOption` classes |

### 1b. The only curve in ArkLib: BN254 (for contrast)

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| base field size | `BN254.baseFieldSize` | `ArkLib/Data/EllipticCurve/BN254.lean:43` | yes | `@[reducible] def ... : Nat` |
| base field | `BN254.BaseField` | `:47` | yes (`abbrev = ZMod ...`) | |
| primality | `BN254.BaseField_is_prime` | `:50` | proof | long Pratt-certificate proof |
| curve | `BN254.curve` | `:152` | yes | `def curve : WeierstrassCurve BaseField` (Y² = X³ + 3) |
| short normal form | `instance : curve.IsShortNF` | `:161` | proof | |
| ellipticity | `instance : curve.IsElliptic` | `:164` | proof | via `WeierstrassCurve.Δ_of_isShortNF` |
| generator | `BN254.generator` | `:176` | yes | `(1, 2) : BaseField × BaseField`; docstring notes some places use `(-1, 2)` |
| on-curve proof | `BN254.generator_on_curve` | `:179` | proof | |
| scalar field | `BN254.ScalarField` (CompPoly) | `CompPoly/Fields/BN254/Basic.lean:26` | yes | ArkLib imports it at `BN254.lean:9` |

File header says **"WARNING: this is experimental. Use with caution!"** (`BN254.lean:15`). It is
imported by `ArkLib.lean:515` and by **nothing else** in the repo (grep `Data.EllipticCurve` ->
1 hit). No G2, no pairing, no r-torsion group structure, no codec.

## 2. ArkLib -- KZG

All under `ArkLib/Commitments/Functional/KZG/`, namespace `KZG`. **Zero `sorry` in the whole
KZG directory** (verified by the sweep in section 7).

### 2a. The scheme

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| group abstraction (stands in for "the curve") | variables `{G₁ G₂ Gₜ : Type} [Group ...] [PrimeOrderWith ... p] [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]` | `Basic.lean:47-51` | -- | **This is the r-torsion / `Module Fr` formalisation**: prime-order groups made into `ZMod p`-modules. Not tied to any concrete curve. |
| pairing | `(pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))` | `Basic.lean:52` | -- | **Bilinearity is by type** (two `LinearMap`s), not a theorem. No pairing is *constructed* anywhere. (The arrow is Lean's linear-map notation with a subscripted ring.) |
| commit | `KZG.commit` | `Basic.lean:58` | yes (`def`) | `Vector G₁ (n+1) → (Fin (n+1) → ZMod p) → G₁`, a product of powers |
| open | `KZG.generateOpening` | `Basic.lean:63` | yes | quotient by `X - z` via `divByMonic` |
| verify | `KZG.verifyOpening` | `Basic.lean:72` | yes (needs `DecidableEq Gₜ`) | returns `Bool`; pairing check in the exponent |
| linearity lemmas | `KZG.lin_fst`, `KZG.lin_snd` | `Basic.lean:123`, `:131` | proofs | `a • pairing g₁ g₂ = pairing (g₁ ^ a) g₂` etc. |
| key algebra lemmas | `KZG.verify_opening_equation` `:164`, `KZG.verify_opening_prf_equation` `:199` | `Basic.lean` | proofs | both **take non-degeneracy as a hypothesis** `hpair : pairing g₁ g₂ ≠ 0` |
| the scheme | `KZG.CommitmentScheme.kzg` | `Basic.lean:234` | yes (`def`) | type: `Commitment.Scheme unifSpec (Fin (n+1) → ZMod p) G₁ Unit (Vector G₁ (n+1) × Vector G₂ 2) (Vector G₁ (n+1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩`; 1 round, prover-to-verifier |
| SRS tower / generate | `Groups.PowerSrs.tower` `:43`, `Groups.PowerSrs.generate` `:48` | `Algebra.lean` | yes | |
| trapdoor sampling | `Groups.sampleNonzeroZMod` | `Sampling.lean:37` | yes | `ProbComp (ZMod p)`; lemma `simulateQ_randomOracle_sampleNonzeroZMod` `:43` |
| prime-order class | `PrimeOrderWith` | `ArkLib/Data/GroupTheory/PrimeOrder.lean:40` | yes (`class`) | single field `hCard : Nat.card G = p`; yields `PrimeOrder`, `IsCyclic`, `CommGroup` |

### 2b. Security theorems

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| correctness (algebraic) | `KZG.correctness` | `Correctness.lean:59` | proof | |
| perfect correctness | `KZG.CommitmentScheme.correctness` | `Correctness.lean:169` | proof | `Commitment.perfectCorrectness (pure ∅) (randomOracle) (kzg ...)` -- **fully proved, no sorry** |
| evaluation binding | `KZG.CommitmentScheme.binding` | `Binding.lean:751` | proof | hypotheses: `hg₁ : g₁ ≠ 1`, `hpair : pairing g₁ g₂ ≠ 0`, `[SampleableType G₁]`, `Groups.tSdhAssumption n tSdhError` yields `Commitment.binding` |
| **function binding** | `KZG.CommitmentScheme.function_binding` | `FunctionBinding/Basic.lean:635` | proof | `(L : ℕ) (hn : 1 ≤ n) (hp : p ≥ n + 2) (hg₁ : g₁ ≠ 1) (hpair : pairing g₁ g₂ ≠ 0) [SampleableType G₁] (arsdhError : ℝ≥0) (hArsdh : Groups.arsdhAssumption n arsdhError) → Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle) (hn := rfl) (kzg ...) arsdhError`. **This is the headline KZG theorem.** |
| function-binding reduction chain | `KZG.CommitmentScheme.reduction` `:118`, `mapFunctionBindingToArsdh` `:100`, `functionBindingGameExt` `:157`, `function_binding_cond_le_arsdh_cond` `:520`, `arsdh_game_eq` `:549`, `arsdh_error_bound` `:623` | `FunctionBinding/Basic.lean` | mixed | supporting files: `FunctionBinding/{DegreeConflict,EvaluationBindingConflict,Support,TauInQueries}.lean` |
| t-SDH | `Groups.tSdhAdversary` `:55`, `tSdhCondition` `:60`, `tSdhGame` `:72`, `tSdhExperiment` `:84` (**noncomputable**), `tSdhAssumption` `:90` | `HardnessAssumptions.lean` | `def ... : Prop`; experiment noncomputable | |
| **ARSDH** | `Groups.arsdhAdversary` `:96`, `arsdhCondition` `:101`, `arsdhGame` `:108`, `arsdhExperiment` `:120` (**noncomputable**), `Groups.arsdhAssumption` `:127` | `HardnessAssumptions.lean` | `def ... : Prop` | docstring: "adaptive rational strong Diffie-Hellman (ARSDH) assumption. Taken from Definition 9.6 in [CGKY25]." Namespace is top-level `Groups`, **not** `KZG.Groups`. |
| commitment-scheme structure | `Commitment.KeyGen` `:52`, `Commitment.Commit` `:56`, `Commitment.Opening` `:62`, `Commitment.Scheme` `:67` (extends all three) | `ArkLib/Commitments/Functional/Basic.lean` | yes (`structure`) | fields: `keygen : OracleComp oSpec (ComKey × VerifKey)`; `commit : ComKey → Data → OracleComp oSpec (Commitment × Decommitment)`; `opening : (ComKey × VerifKey) → Proof oSpec (Commitment x (q : O.Query) x O.Response q) (Data × Decommitment) pSpec` |
| security predicates | `Commitment.correctness` `:93`, `perfectCorrectness` `:112`, `binding` `:219`, `extractability` `:249`, `functionBinding` `:348` | same file | inside `noncomputable section` (`:74`) | `extractability` takes `(_extractabilityError : ℝ≥0)` -- **underscored = unused**, extractability is not yet wired to a bound |

### 2c. Algebraic Group Model (AGM)

**AGM is a stub.** `ArkLib/AGM/Basic.lean` is 202 lines and contains **no theorem** connecting
adversary success to a representation.

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| representation | `AGM.GroupRepresentation` | `AGM/Basic.lean:35` | yes (`structure`, `@[ext]`) | fields `exponents : ι → ZMod p`, `hEq : (∏ i, basis i ^ (exponents i).val) = target` |
| helpers | `AGM.GroupRepresentation.pow_val_add` `:45`, `modulus_pos` `:52` | | proofs | |
| value table | `AGM.GroupValTable` | `:68` | yes | `Π₀ _ : ι, Option G` (DFinsupp, "since it's computable, unlike Finsupp") |
| group oracles | `AGM.OracleSpec.GroupOpOracle` `:77`, `GroupExpOracle` `:85`, `GroupEqOracle` `:90`, `GroupEncodeOracle` `:96`, `GroupDecodeOracle` `:101` | | yes | encode/decode via `BitVec bitLength` |
| oracle impls | `implGroupOpOracle` `:112`, `implGroupExpOracle` `:121`, `implGroupEqOracle` `:129`, `implGroupEncodeOracle` `:141`, `implGroupDecodeOracle` `:151` | | yes | need `Serialize G (BitVec bitLength)` / `DeserializeOption` |
| adversary | `AGM.Adversary` | `:174` | yes (`def ... : Type`) | `ReaderT (GroupValTable ι G) (OracleComp (GroupOp + GroupExp + GroupEq + GroupEncode)) (List ι × α)` |
| adversary runner | `AGM.Adversary.run` | `:189` | def but **`sorry`** at `:190` | docstring: "TODO: need to be sure this definition is correct." |
| `algebraicGroupModel` | **not found** | -- | -- | grep returns 0 hits; only `GroupRepresentation` |
| AGM in the pairing setting | **not found** | -- | -- | `AGM/Basic.lean:200`: "-- TODO: talk about AGM in the pairing setting" |
| AGM-to-KZG soundness link | **not found** | -- | -- | KZG proofs use plain group hypotheses, never the AGM oracle machinery |

Test coverage: `ArkLibTest/AGM/Basic.lean` only builds toy `GroupRepresentation`s
(zero / singleton / two-coordinate) -- no axiom check, no security theorem.

### 2d. Interactive-oracle reduction layer

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| protocol spec | `ProtocolSpec` | `ArkLib/OracleReduction/ProtocolSpec/Basic.lean:31` | yes (`structure`, `@[ext]`, `deriving Inhabited`) | fields `dir : Fin n → Direction`, `Type : Fin n → Type` (written with back-quotes in Lean); `MessageIdx` `:52`, `ChallengeIdx` `:57`, `empty` / notation `!p[]` `:46` |
| reduction | `Reduction` | `ArkLib/OracleReduction/Basic.lean:655` | yes | `{ prover, verifier }` |
| oracle reduction | `OracleReduction` | `ArkLib/OracleReduction/Basic.lean:663` | yes (`@[ext] structure`) | fields `prover : OracleProver ...`, `verifier : OracleVerifier ...`; `OracleReduction.toReduction` `:675`; `OracleReduction.id` `:819`; `run`/`runWithLog` in `Execution.lean:434,449` |
| knowledge soundness (named extractor) | `Verifier.knowledgeSoundnessWith` | `ArkLib/OracleReduction/Security/Basic.lean:298` | `def ... : Prop` (file is in `noncomputable section` at `:31`) | straightline extractor kept in the statement; probability written `Pr{...}[...] ≤ knowledgeError` |
| knowledge soundness | `Verifier.knowledgeSoundness` | `Security/Basic.lean:343` | `def : Prop` | existential over the extractor; `knowledgeSoundness_iff_exists_with` `:364`, `knowledgeSoundness_of_with` `:373` |
| oracle-verifier variants | `OracleVerifier.knowledgeSoundnessWith` `:486`, `OracleVerifier.knowledgeSoundness` `:497`, `knowledgeSoundness_of_with` `:505` | same file | `def : Prop` | |
| round-by-round knowledge soundness | `Verifier.rbrKnowledgeSoundness` | `Security/RoundByRound.lean:457` (namespace `Verifier` at `:145`) | `def : Prop` | exists `WitMid`, exists `extractor : Extractor.RoundByRound ...`, exists `kSF : verifier.KnowledgeStateFunction ...`; error is a function `pSpec.ChallengeIdx → ℝ≥0`. Also `rbrKnowledgeSoundnessWorstCase` and `rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness` `:642` |
| rbr implies knowledge soundness | `Verifier.rbrKnowledgeSoundness_implies_knowledgeSoundness` | `Security/Implications.lean:189` | **`sorry`** at `:194` | |
| knowledge implies soundness | `Verifier.knowledgeSoundness_implies_soundness` | `Security/Implications.lean:49` | **`sorry`** at `:63` | |
| Fiat-Shamir prover | `Prover.fiatShamir` | `OracleReduction/FiatShamir/Basic.lean:114` | yes | docstring: "The (slow) Fiat-Shamir transformation for the prover." |
| Fiat-Shamir verifier | `Verifier.fiatShamir` | `FiatShamir/Basic.lean:130` | yes | |
| Fiat-Shamir reduction | `Reduction.fiatShamir` | `FiatShamir/Basic.lean:140` | yes | |
| Fiat-Shamir **completeness** | `fiatShamir_completeness` | `FiatShamir/Basic.lean:163` | **`sorry`** at `:173` | |
| Fiat-Shamir **soundness / knowledge soundness** | **not found** | -- | -- | no `fiatShamir_soundness` / `fiatShamir_knowledgeSoundness` anywhere in the repo. Single biggest structural gap for a KZG + Fiat-Shamir pipeline. |
| duplex-sponge FS | `DuplexSpongeFS.*` | `FiatShamir/DuplexSponge/*` | mostly `sorry` | `State.lean` `generateTag/absorb/squeeze/hint/ratchet` all `sorry` (`:87,111,123,135,147`); `Security/KeyLemma.lean:122` `duplexSpongeToFSGameStatDist` = `sorry` |
| sequential-composition security | `Verifier.append_soundness` `:49`, `append_knowledgeSoundness` `:60`, `append_rbrSoundness` `:81`, `append_rbrKnowledgeSoundness` `:96` | `OracleReduction/Composition/Sequential/Append/Security.lean` | **all `sorry`** | |

## 3. VCVio

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| oracle specification | `OracleSpec` | `VCVio/OracleComp/OracleSpec.lean:29` | yes | `def OracleSpec (ι : Type u) : Type (max u (v+1)) := ι → Type v`; `attribute [implicit_reducible] OracleSpec` `:44` |
| random oracle (lazy) | `OracleSpec.randomOracle` | `VCVio/OracleComp/QueryTracking/RandomOracle/Basic.lean:24` | yes (`@[inline, reducible] def`) | `QueryImpl spec (StateT spec.QueryCache ProbComp) := uniformSampleImpl.withCaching`; needs `[DecidableEq ι]` + `[forall t, SampleableType (spec.Range t)]`. Cache-step law `randomOracle.run_eq` `:43` |
| eager random oracle / ROM tables | `tableExtending` `:54`, `evalDist_simulateQ_randomOracle_run'_eq_tableExtending` `:130` | `VCVio/OracleComp/QueryTracking/RandomOracle/EagerTable.lean` | yes / proofs | also `romImpl` at `RandomOracle/Simulation.lean:207` |
| logging oracle | `OracleSpec.loggingOracle` | `VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean:311` | yes | `QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec))`; `loggingOracle.fst_map_run_simulateQ` `:318` proves logging does not change behaviour |
| query log | `QueryLog` | `VCVio/OracleComp/QueryTracking/Structures.lean:382` | yes (`@[reducible] def`) | `List ((t : spec.Domain) x spec.Range t)`; `singleton` `:388`, `logQuery` `:392` |
| oracle simulation | `simulateQ` | `VCVio/OracleComp/SimSemantics/SimulateQ.lean:30` | yes | `QueryImpl spec r → OracleComp spec alpha → r alpha`; bundled `simulateQ'` `:48` |
| probability notation | `prEvent` + `Pr{...}[...]` | `VCVio/EvalDist/ProbabilityNotation.lean:39` (def), `:63` (syntax) | **noncomputable** | syntax is `Pr{ doSeq }[ term ]`. **There is no bare `Pr[...]` form** -- braces hold the do-sequence, brackets the event. `prFail` `:54` also noncomputable |
| keccak256 | `VCVio.Algorithms.Keccak.keccak256` | `VCVio/Algorithms/Keccak.lean:127` | **yes -- pure Lean, FFI-free** | `def keccak256 (input : ByteArray) : ByteArray := squeeze (absorb input 136 0x01) 32` (EVM domain byte `0x01`). Built on `f1600` `:67`, `round` `:53`, `absorb` `:71`, `squeeze` `:86`. Also `sha3Digest256` `:130`, `shake128/256` `:142,147` |
| keccak via FFI? | **not found** | -- | -- | `Extern/Hashing.lean:24-37` exposes only `sha3_256`, `sha3_512`, `shake256`, `shake128` as `@[extern]` opaques (mlkem-native C in `csrc/hashing/lean_hashing_ffi.c`). No keccak256 FFI binding |
| keccak wired as an oracle impl? | **not found** | -- | -- | grep `keccak256` over `VCVio/**` hits only `Algorithms/Keccak.lean`; it is never installed as a `QueryImpl` |
| toolchain | `leanprover/lean4:v4.35.0` | `lean-toolchain` | -- | mathlib tag `v4.35.0` |
| `sorry` | `euf_cma_bound` | `VCVio/CryptoFoundations/FiatShamir/WithAbort/Security.lean:109` (sorry at `:131`) | proof | **the only in-code `sorry` under `VCVio/**`** (1 raw hit, 1 in code). Docstring: "The proof is intentionally deferred." |
| axiom status | not executed | -- | -- | VCVio is mathlib-based; expect `[propext, Classical.choice, Quot.sound]` plus the one `sorry` above. Not verified here (no build). |

## 4. CompPoly (transitive dep, pinned by ArkLib)

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| field set | `CompPoly.Fields.{BLS12_377, BLS12_381, BN254, BabyBear, Goldilocks, KoalaBear, Mersenne31, Montgomery, Pasta, Secp256k1, Binary, Hachi, Extension}` | `CompPoly/Fields/` | yes | BLS12-381 = scalar field only (see 1a) |
| generic extension fields | `ExtensionParams` `:49`, `Ext` `:88`, `gen` `:160`, `inv` `:445`; `instCommRing` `Bridge.lean:311`, `instAlgebra` `Bridge.lean:364` | `CompPoly/Fields/Extension/Arithmetic.lean` | yes | computable binomial extensions + a `ByteCodec` instance -- the natural place to build Fp2/Fp12 |
| byte codec class | `CompPoly.ByteCodec` | `CompPoly/Data/Bytes/Codec.lean:33` | yes (`class`) | derives `Serialize`/`DeserializeOption` instances at `:88-100` |
| serialize classes | `CompPoly.Serialize` `:28`, `Serialize.IsInjective` `:34`, `Deserialize` `:39`, `DeserializeOption` `:44` | `CompPoly/Data/Classes/Serialize.lean` | yes | these are what ArkLib's AGM oracles consume |
| `sorry` | **none** | -- | -- | 5 raw grep hits, **0 in code** (all docstring prose such as "sorry-free") |
| build note | `preferReleaseBuild := true`, `releaseRepo := "https://github.com/Verified-zkEVM/CompPoly"`, `buildArchive := "CompPoly-oleans.tar.gz"`, `platformIndependent := true` | `lakefile.lean` | -- | downstream consumes **prebuilt oleans** from GitHub releases rather than compiling from source |

## 5. powdr-labs/yul-semantics at `c9914c1`

Toolchain `leanprover/lean4:v4.33.0`; deps = **Batteries only** (`lakefile.toml`, rev `v4.33.0`,
manifest hash `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`), and only for the lint driver --
"No library module imports it". `warningAsError = true`. **Zero `sorry`** (0 raw hits under
`YulSemantics/**`). 19 files, about 5.6 kLoC.

### 5a. AST (`YulSemantics/Ast.lean`, namespace `YulSemantics`)

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| identifier | `YulSemantics.Ident` | `Ast.lean:30` | yes | `abbrev Ident := String` |
| literal | `YulSemantics.Literal` | `:38` | yes (`inductive`, `DecidableEq`) | `number / bool / string` |
| expression | `YulSemantics.Expr (Op : Type)` | `:52` | yes (`inductive`) | `lit / var / builtin op args / call fn args` |
| statement | `YulSemantics.Stmt (Op : Type)` | `:64` | yes | `block, funDef, letDecl, assign, cond, switch, forLoop, exprStmt, break, continue, leave` (the last three use Lean back-quote identifiers) |
| block | `YulSemantics.Block (Op : Type)` | `:90` | yes | `abbrev Block := List (Stmt Op)` |
| object | `YulSemantics.Object (Op : Type)` | `:327` | yes (`inductive`) | `mk (name : String) (code : Block Op) (subObjects : List (Object Op)) (data : List (String x Data))` |
| object accessors | `Object.name` `:335`, `Object.codeBlock` `:337`, `Object.subObjects` `:339`, `Object.dataSegs` `:342` | | yes | `dataSegs` renamed to dodge the DSL keyword |
| data segment | `YulSemantics.Data` | `:320` | yes | `hex (List UInt8) / string (String)` |
| outcome | `YulSemantics.Outcome` | `:353` | yes | `normal / break / continue / leave / halt` |
| executable syntactic equality | `SyntaxEq.exprBeq` `:106`, `SyntaxEq.stmtBeq` `:131`, soundness `SyntaxEq.exprBeq_eq` `:174`, `SyntaxEq.stmtBeq_eq` `:214` | | yes | hand-rolled because deriving cannot see through mutual `List` recursion |
| surface DSL | `yul%` / `yulObject%` | `YulSemantics/Syntax.lean` | yes | plus `PrettyPrint.lean` |

### 5b. Semantics, interpreter, adequacy

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| big-step judgment | `YulSemantics.Step (D : Dialect)` | `BigStep.lean:164` | `inductive` (Prop) | single indexed judgment over `Code` `:141` / `Res` `:155`; the five conceptual relations are abbreviations `EvalExpr` `:340`, `EvalArgs` `:345`, `ExecStmt` `:350`, `ExecStmts` `:355`, `ExecLoop` `:360` |
| whole-program run | `YulSemantics.Run` | `BigStep.lean:366` | Prop | `ExecStmt D [] [] st0 (.block prog) V' st' o` |
| environments | `VEnv` `:66`, `FDecl` `:69`, `FScope` `:78`, `FunEnv` `:81` | | yes | |
| dialect class | `YulSemantics.Dialect` | `Dialect.lean:108` | yes (`structure`) | fields `Value, State, Op, litValue, Builtin, Effects : Op → Effects`; record `Effects` `:60` (`deterministic/reads/writes/halts`); `Dialect.Deterministic` `:135`, `NonWriting` `:139`, `NonHalting` `:143`; `Dialect.EffectsSound` `:160` |
| executable dialect | `YulSemantics.ExecDialect` | `Dialect.lean:176` | yes | extends `Dialect` with `builtinFn`; `ExecDialect.Lawful` `:184` |
| interpreter | `YulSemantics.Interp.run` | `Interp.lean:212` | **yes (total, fuel-indexed)** | `run (fuel : ℕ) (prog : Block E.toDialect.Op) (st0) : Result (SResult E)`; `Result` inductive `:24` (`ok / stuck / outOfFuel`) |
| adequacy (generic) | `Interp.run_adequacy` | `Adequacy.lean:772` | proof | `Run E.toDialect prog st0 V' st' o ↔ ∃ n, Interp.run E n prog st0 = .ok (V', st', o)`; soundness `run_sound` `:452`, completeness `complete` `:473`, judgment-level `adequacy` `:740` |
| adequacy (EVM, hypothesis-free) | `EVM.run_adequacy` | `Adequacy.lean:786` | proof | from `Interp.run_adequacy EVM.exec_lawful`. **Closed-world `EVM.evm` only** -- README states there is no adequacy for `evmWithExternal` |
| determinism | `Step.det` `Determinism.lean:22`, `Run.det` `:411`, `EVM.evm_deterministic` `:419`, `EVM.run_det` `:427` | | proofs | |
| Hoare-style contracts | `RunContract` | `Contract.lean:21` | Prop (`def`) | `RunContract (program : Block D.Op) (pre : D.State → Prop) (post : ...) : Prop`; combinators `intro` `:31`, `consequence` `:41`, `and_post` `:55`, `map_program` `:71`, `RunContract.of_stmts` `:205`; also `StmtContract` `:85`, `StmtsContract` `:94` |
| committed observation | `RunCommitted` | `Observation.lean:39` | Prop (`def`) | `RunCommitted (prog : Block EVM.Op) (st0 : EvmState) (V' : VEnv EVM.evm) ...`; **`RunCommitted.det`** `:45` proves functionality (via `EVM.run_det`); `committedState` `Dialect/EVMExec.lean:262`, `HaltKind.commits` `:250` |
| objects / layout | `YulSemantics/Object.lean`, `ObjectRun.lean` | | yes | name resolution, a layout-consistency predicate, and a symbolic proof that the canonical constructor (datacopy then return) returns a data segment's bytes |

### 5c. EVM dialect specifics

| item | exact Lean name | file:line | computable? | notes |
|---|---|---|---|---|
| word type | `YulSemantics.EVM.U256` | `Dialect/EVMOp.lean:23` | yes | `abbrev U256 := BitVec 256` |
| builtin ops | `YulSemantics.EVM.Op` | `Dialect/EVMOp.lean:27` | yes (`inductive`) | full EVM builtin set through Fusaka (`clz`, `mcopy`, `blobhash`, `blobbasefee`); `keccak256` case at `:35`; classification `effects` `:88`; parser `parse` `:173` |
| closed-world dialect | `EVM.evm` | `Dialect/EVMExec.lean:942` | yes (`def : Dialect`) | `gas()` and the call/create family are **stuck** (`stepOp` returns `none`, see `:832`) |
| executable dialect | `EVM.exec` | `Dialect/EVMExec.lean:969` | yes | `{ toDialect := evm, builtinFn := stepOp }`; `EVM.exec_lawful` at `Dialect/EVM.lean:92` |
| **open-world dialect** | `EVM.evmWithExternal (calls : ExternalCalls) (creates : ExternalCreates) (gasOracle : ExternalGas) : Dialect` | `Dialect/EVMExec.lean:953` | yes (`def`) | `Builtin := builtinWithExternal calls creates gasOracle` (`:878`); `evmWithCalls` `:964` |
| external calls | `ExternalCalls` | `Dialect/EVMExec.lean:472` | yes (`structure ... : Prop`) | single field `Call : CallRequest → EvmState → CallResponse → Prop`; `ExternalCalls.none` `:480` (always False), `ExternalCalls.any` `:484` (always True). **Relational, possibly nondeterministic** -- describes *completed* executions, so nested calls and re-entrancy are absorbed |
| external creates | `ExternalCreates` | `:525` (`none` `:532`, `any` `:535`) | yes | `Create : CreateRequest → EvmState → CreateResponse → Prop` |
| gas oracle | `ExternalGas` | `:549`, `any` `:557`, `none` `:561`, `ofFun` `:564` | yes | **`gas()` is nondeterministic**: `builtinWithExternal` `:926` -- the `.gas` case is "exists g : U256, gasOracle.Gas st g and result = .ok [g] st". With `ExternalGas.none` it is stuck (proved at `Dialect/EVM.lean:263`) |
| gas accounting | **not modelled** | README "Gas is not modeled"; `DESIGN.md` section 1 | -- | no gas field in `EvmState`; only `gasprice`/`gaslimit` environment reads (`ExecEnv` `:124,147`) |
| **keccak256 modelling** | `EVM.keccakBytes : List UInt8 → U256` | `Dialect/EVMExec.lean:88` | **`opaque`** | i.e. an **axiom-backed abstract function**, "deterministic but unspecified". Installed as the default of `ExecEnv.keccakOf : List UInt8 → U256` (`:160`); used by `stepOp` at `:731-732` (hash of the requested memory slice) and for `extcodehash` (`:298`). Clients may install a concrete implementation |
| environment modelling | `EVM.ExecEnv` | `Dialect/EVMExec.lean:114` | yes (`structure`, all fields defaulted) | about 30 fields: `address, origin, caller, callvalue, gasprice, selfBalance, createdThisTx, static, coinbase, timestamp, number, prevrandao, gaslimit, chainid, basefee, blobbasefee, calldata, code, keccakOf, balanceOf, extCodeOf, extCodeHashOf, nonceOf, storageOf, transientOf, blockHashOf, blobHashOf, dataOffset, dataSize, immutable` |
| machine state | `EVM.EvmState` | `:205`, `EvmState.init` `:230` | yes | `memory : ℕ → UInt8`, `activeWords` (msize high-water), `storage`, `transient`, `env`, `returndata`, `logs : List LogEntry` (`LogEntry` `:96`), `selfdestructs : List (U256 × Bool)`, `halted` |
| static-call protection | `EVM.guardStatic` | `:692` | yes | sstore/tstore/log*/selfdestruct/create/value-bearing call halt exceptionally |
| effect-classification soundness | `EVM.effects_sound` `Dialect/EVM.lean:98`, `EVM.effects_sound_withExternal` `:135`, `EVM.effects_sound_withCalls` `:178` | | proofs | **the only meta-theorem that carries over to the open world** |
| precompiles | **not found** | -- | -- | case-insensitive grep for `precompile` over `YulSemantics/**` and `DESIGN.md` returns **0 hits**. No ecrecover / sha256 / ripemd160 / modexp / ecadd / ecmul / bn254-pairing / point-eval ops |
| `#print axioms` | **not found** | -- | -- | no axiom assertions in the repo; note `opaque keccakBytes` is itself an axiom-like constant, so any statement mentioning the default `ExecEnv` keccak depends on it |

## 6. mathlib: does it have BLS12-381?

**No.** Checked against the live `leanprover-community/mathlib4` file tree (GitHub trees API,
10790 paths, `truncated: false`):

- paths containing `bls`: **0**
- paths containing `bn254`: **0**
- paths containing `miller`: **0** (no Miller loop, hence no Weil/Tate/Ate pairing)
- `pairing`: 12 paths, all unrelated (`Mathlib/Data/Nat/Pairing.lean`, `LinearAlgebra/PerfectPairing/*`, simplicial, root systems, tensor powers)
- elliptic curves: `Mathlib/AlgebraicGeometry/EllipticCurve/{Affine/{Basic,Point,Formula,AddSubMap}, Jacobian/*, DivisionPolynomial/*, Weierstrass, IsomOfJ, LFunction}.lean` -- general Weierstrass/Jacobian theory only

So mathlib supplies the *language* (`WeierstrassCurve`, `ZMod`, `Module`, `LinearMap`) that
ArkLib's BN254 file already uses, but **no pairing-friendly curve instantiation and no pairing**.

## 7. ArkLib `sorry` census

Swept every `.lean` file under `arklib/ArkLib/` (1071 files) with a comment/docstring-aware
scanner. Raw word-boundary `sorry` hits: **168**. Of those, **133** are in code position and
**112** are genuine proof-term or `:= sorry` occurrences (the remaining 21 are commented-out
drafts prefixed with `--` and docstring prose such as "sorry-free").

Independent corroboration: ArkLib ships a **kernel-level** accounting tool
(`scripts/AxiomSweep.lean`, wired as `lake exe axiomsweep --check`) plus a committed baseline
`scripts/axiom_baseline.json`:

- key `"sorry"`: **205 declaration names** (transitively `sorryAx`-tainted as the kernel sees it;
  larger than the source count because structure fields, autoparams and compiler-generated
  auxiliaries are included).
- key `"nonstandard"`: **0** -- nothing in ArkLib depends on an axiom beyond
  `propext, Classical.choice, Quot.sound`. No `native_decide`-minted axioms.

Where the 112 in-code sorries live (file: lines):

| count | file |
|---|---|
| 13 | `ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`: 284, 292, 297, 304, 325, 573, 579, 883, 894, 906, 919, 929, 935 |
| 10 | `ArkLib/OracleReduction/LiftContext/Reduction.lean`: 125, 190, 200, 333, 365, 437, 494, 499, 536, 554 |
| 9 | `ArkLib/OracleReduction/Security/Implications.lean`: 63, 83, 194, 235, 236, 250, 251, 265, 279 |
| 6 | `ArkLib/Commitments/Functional/Hachi/Recursion/PartialEval.lean`: 94, 100, 111, 120, 198, 221 |
| 6 | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean`: 48, 118, 139, 154, 201, 219 |
| 5 | `ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean`: 87, 111, 123, 135, 147 |
| 4 | `ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean`: 93, 106, 193, 242 |
| 4 | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/WeightedAgreement.lean`: 81, 113, 155, 185 |
| 4 | `ArkLib/OracleReduction/Composition/Sequential/Append/Security.lean`: 55, 68, 90, 105 |
| 4 | `ArkLib/ProofSystem/Spartan/Basic.lean`: 245, 333, 364, 376 |
| 4 | `ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean`: 77, 308, 317, 338 |
| 3 | `ArkLib/Commitments/Functional/Hachi/Recursion/ZBatchBridge.lean`: 84, 121 (+1 docstring) |
| 3 | `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean`: 50, 195, 226 |
| 3 | `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean`: 219, 255, 276 |
| 3 | `ArkLib/ProofSystem/BatchedFri/Security.lean`: 266, 693, 783 |
| 2 | `.../BCIKS20/ListDecoding/Extraction.lean`: 66, 79 |
| 2 | `.../ListDecodability/Bounds/ReedSolomon.lean`: 90, 613 |
| 2 | `.../FiatShamir/DuplexSponge/Security/Backtrack.lean`: 80, 113 |
| 2 | `.../FiatShamir/DuplexSponge/Security/Lookahead.lean`: 91, 134 |
| 2 | `.../FiatShamir/DuplexSponge/Security/ProverTransform.lean`: 34, 45 |
| 2 | `ArkLib/ProofSystem/Stir/MainThm.lean`: 145 (`stir_main`), 227 (`stir_rbr_soundness`) |
| 2 | `ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean`: 94, 104 |
| 1 each | `ArkLib/AGM/Basic.lean:190` (`AGM.Adversary.run`) - `ArkLib/Commitments/Functional/Hachi/Commitment.lean:153` (`hachi`'s `opening := sorry`) - `ArkLib/OracleReduction/Basic.lean:537` (`OracleVerifier.numQueries`) - `ArkLib/OracleReduction/FiatShamir/Basic.lean:173` (`fiatShamir_completeness`) - `.../DuplexSponge/Security/KeyLemma.lean:122` - `.../DuplexSponge/Security/TraceTransform.lean:40` - `ArkLib/Data/Fin/Basic.lean:337` (`Fin.sumCases`) - `ArkLib/Data/MvPolynomial/Interpolation.lean:250` (`MvPolynomial.basis`) - `ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:149` (`Plonk.ConstraintSystem.perm`) - `ArkLib/ProofSystem/Component/NoInteraction.lean:91` - `ArkLib/ProofSystem/Component/SendWitness.lean:406` - `ArkLib/ProofSystem/Stir/ProximityGap.lean:55` - `ArkLib/ProofSystem/BatchedFri/Spec/General.lean:52` - `.../BCIKS20/AffineLines/Main.lean:49` - `.../BCIKS20/ListDecoding/Guruswami.lean:1158` - `.../Connections/ListDecodingAndCA.lean:251` - `.../Bounds/Linear.lean:946` - `.../ProximityGenerator/PolynomialGenerator.lean:298` - `.../ProximityGenerator/TensorGenerator.lean:254` |

**KZG directory: 0 sorries.** `ArkLib/Commitments/Functional/KZG/**` is entirely sorry-free, and no
KZG declaration appears in `scripts/axiom_baseline.json`'s tainted list.

`#print axioms` usage: 253 occurrences in `ArkLibTest/` (all for Hachi/lattice results), **none
for KZG or AGM**. So the axiom cleanliness of `KZG.CommitmentScheme.function_binding` is *inferred*
from (a) zero sorries in its file chain and (b) `nonstandard: []` in the committed kernel baseline;
expected `[propext, Classical.choice, Quot.sound]`, **not directly observed**.

## 8. GAPS

| # | gap | evidence | suggested workaround |
|---|---|---|---|
| 1 | **No BLS12-381 anywhere in ArkLib** -- not even a mention. | case-insensitive grep `bls` over ArkLib = 0 hits | Use CompPoly's `BLS12_381.ScalarField` for Fr and build Fq/Fp2/Fp12 on top of CompPoly's generic `Fields.Extension.{ExtensionParams, Ext}` + `ByteCodec` machinery |
| 2 | **No pairing formalisation in ArkLib, CompPoly, VCVio or mathlib.** | no `def pairing` anywhere; mathlib tree has no `miller` and no EC-pairing file | Instantiate ArkLib's pairing *parameter* (the `LinearMap`-typed one at `KZG/Basic.lean:52`) with a concrete pairing we define; ArkLib's theorems stay valid for any such `pairing` satisfying the two side hypotheses |
| 3 | **No G1/G2/GT point types, no r-torsion group, no curve equation for BLS12-381.** | section 1a "not found" rows | Define `G1 := { p : Fp2 × Fp2 // onCurve p }` via mathlib `WeierstrassCurve` (ArkLib's BN254 file is the template), then supply `PrimeOrderWith G₁ p` + `Module (ZMod p) (Additive G₁)` instances -- exactly the interface KZG consumes |
| 4 | **No point compression / encoding codec for curve points.** | only field codecs (`instByteCodecZMod`, `ByteCodec (Ext P)`) | Write `ByteCodec G₁`/`ByteCodec G2` instances (x-only + sign bit) against `CompPoly.ByteCodec`; ArkLib's AGM oracles already accept any `Serialize`/`DeserializeOption` pair |
| 5 | **Non-degeneracy is a hypothesis, never proved.** | `hpair : pairing g₁ g₂ ≠ 0` in `Binding.lean:751`, `FunctionBinding/Basic.lean:635`, `Basic.lean:164,199` | Acceptable for a generic-scheme proof; for a concrete instantiation we must discharge `pairing g₁ g₂ ≠ 0` ourselves once a pairing exists (gap 2) |
| 6 | **AGM is a stub:** `AGM.Adversary.run = sorry`, no AGM soundness theorem, no pairing-setting AGM. | `AGM/Basic.lean:190`; TODO comments at `:172, 194-200` | Do not build on ArkLib AGM. Either use only the plain-group hypotheses KZG actually needs, or formalise the AGM extraction step ourselves on top of `AGM.GroupRepresentation` |
| 7 | **No Fiat-Shamir soundness/knowledge-soundness theorem in ArkLib** -- only `fiatShamir_completeness`, and it is `sorry`. | `FiatShamir/Basic.lean:163` / `:173` | Biggest pipeline risk. Prove FS soundness ourselves against `Verifier.knowledgeSoundness`, or import it from VCVio's `CryptoFoundations/FiatShamir/*` (which has its own deferred `euf_cma_bound`) |
| 8 | **Composition/implication glue is admitted:** `append_{soundness,knowledgeSoundness,rbrSoundness,rbrKnowledgeSoundness}`, `knowledgeSoundness_implies_soundness`, `rbrKnowledgeSoundness_implies_knowledgeSoundness`, all `liftContext_*` = `sorry`. | `Composition/Sequential/Append/Security.lean:55,68,90,105`; `Security/Implications.lean:63,83,194,...`; `LiftContext/Reduction.lean` (10) | Restrict to the single-protocol path (KZG then `function_binding`); avoid sequential-composition and lift-context lemmas until proved |
| 9 | **Sumcheck spec is heavily `sorry`d** (13 in `Sumcheck/Spec/SingleRound.lean`), as are BatchedFri, STIR (`stir_main`, `stir_rbr_soundness`), Spartan, Plonk `perm`. | section 7 table | Do not plan on reusing ArkLib's sumcheck/FRI/STIR soundness in this phase |
| 10 | **Toolchain split:** ArkLib/VCVio/CompPoly = Lean v4.35.0 vs yul-semantics = v4.33.0. | `lean-toolchain` files | Pin everything to v4.35.0 and send yul-semantics a bump PR (it is Batteries-only, so the bump surface is small), or vendor its 19 files |
| 11 | **yul-semantics models no gas and no precompiles.** | README "Gas is not modeled"; grep `precompile` = 0 hits; `gas()` is an `ExternalGas` relation (`EVMExec.lean:549, 926`) | For halo2-style functional-equivalence work this is acceptable. Precompiles must be added as new `EVM.Op` cases or modelled as extra `ExternalCalls` relations |
| 12 | **yul-semantics adequacy/determinism do not cover the open world.** | README "Scope of the meta-theory (important)"; `EVM.run_adequacy` is stated for `EVM.evm` only | Keep proofs inside closed-world `EVM.evm`/`EVM.exec` where possible; for calls work relationally with `ExternalCalls` and only `effects_sound_withExternal` |
| 13 | **yul-semantics `keccak256` is an `opaque` axiom, not a real hash.** | `Dialect/EVMExec.lean:88` | Install `ExecEnv.keccakOf := fun bs => VCVio.Algorithms.Keccak.keccak256 (ByteArray.ofList bs)` (VCVio's is pure-Lean and executable, `Keccak.lean:127`) and prove the bridge lemma; note gap 10 blocks importing VCVio into a 4.33 build |
| 14 | **No executed `#print axioms` evidence for the KZG theorems.** | 0 KZG hits under `ArkLibTest/` | Run `lake build && lake exe axiomsweep --check` (or `#print axioms KZG.CommitmentScheme.function_binding`) once we have a working 4.35.0 build |
| 15 | **ArkLib's URL in the brief is wrong** (`arkworks-rs/ArkLib` returns 404). | GitHub API 404; `Verified-zkEVM/ArkLib` works | Use `https://github.com/Verified-zkEVM/{ArkLib,VCVio,CompPoly}` in our `lakefile.toml` |
| 16 | CompPoly expects **prebuilt release oleans** (`preferReleaseBuild := true`, `buildArchive := "CompPoly-oleans.tar.gz"`). | `comppoly/lakefile.lean` | Our build will download a release tarball instead of compiling CompPoly -- good for CI speed, but it means trusting a binary artifact unless we force a source build |


## 9. Non-vacuity model for AdmissiblePairing (attempted, parked)

D-P1 consequence 3 promised a constructed model of Midfall.AdmissiblePairing so
the abstract layer is not vacuous. Attempted and parked after hitting a concrete
ecosystem gap:

* Multiplicative (ZMod p) gives a Group of order p, and PrimeOrderWith _ p is
  easy (Nat.card_eq_fintype_card).
* But the KZG shape also needs Module (ZMod p) (Additive (Multiplicative (ZMod p)))
  - the exponentiation action - and mathlib provides NO such transport instance
  for the Additive/Multiplicative type tags (greps for Module R (Additive,
  Additive.instModule and Multiplicative.instModule across Mathlib return
  nothing). It can be defined by hand, with smul spelled as
  Additive.ofMul (Multiplicative.ofAdd (a * toAdd (toMul x))), and the module
  axioms then reduce to ring facts; but the LinearMap fields need the same
  unfolding through show, and it became instance plumbing rather than
  mathematics.

Update (2026-10-23, while porting msm.rs): two facts narrow this work
package considerably.

* ArkLib's PrimeOrderWith G p carries only hCard : Nat.card G = p
  (ArkLib/Data/GroupTheory/PrimeOrder.lean:47-50) and *derives* PrimeOrder G,
  which provides IsCyclic G and CommGroup G (:29-31). So for
  G := Multiplicative (ZMod p) the AddCommMonoid (Additive G) that the Module
  superclass wants is already there - the ONLY missing piece is the scalar
  action itself, not the whole additive structure. That is why
  Midfall/Halo2/Exec/Kzg/Msm.lean can write gsmul as
  Additive.toMul (s • Additive.ofMul Q) against a plain
  [Module (ZMod p) (Additive G₁)] hypothesis.
* AdmissiblePairing now takes Gₜ as an outParam and carries decEqG₁ / decEqGₜ
  as fields (docs/design.md D-P7). A constructed model must supply both, which
  for Multiplicative (ZMod p) is trivial (decidable equality transports along
  Additive/Multiplicative).

Neither removes the hand-written Module transport, so it stays parked; but it is
now ~20 lines of instance plumbing plus a bilinear map, not an open question.
Action: revisit as its own work package (nice-to-have, not on the M1 or M0 path).
The cheaper non-vacuity argument is that AdmissiblePairing is a *signature*
constraint, not an existence claim: the statements are implications, and the
concrete instance arrives with Assumptions/Pairing.lean.

## 10. yul-semantics, measured against the vendored fork (Phase 5 groundwork)

Sections 0-9 surveyed a fresh clone that was never built. This section reads the
**actual vendored copy** at formal/vendor/yul-semantics (upstream rev c9914c1,
bumped to v4.35.0 per D-P2), which is what Midfall compiles against: 3,948 lines
across 15 modules. Six of the plan's Section 3 inventory items resolve, and five
of the plan's Section 7 / 9.5 type-level assumptions do not. Every file:line was
read from these files.

| plan item | actual name | file:line |
|---|---|---|
| AST, Object | inductive Object (Op : Type) | Ast.lean:327 |
| ExternalCalls | structure ExternalCalls where Call : CallRequest -> EvmState -> CallResponse -> Prop | Dialect/EVMExec.lean:472 |
| EVM.evmWithExternal | def evmWithExternal (calls) (creates) (gasOracle) : Dialect | Dialect/EVMExec.lean:953 |
| (two-arg shorthand) | def evmWithCalls (external) = evmWithExternal external ExternalCreates.none ExternalGas.any | Dialect/EVMExec.lean:964 |
| RunContract | def RunContract (program) (pre : D.State -> Prop) (post : D.State -> VEnv D -> D.State -> Outcome -> Prop) | Contract.lean:21 |
| RunCommitted | def RunCommitted (prog : Block EVM.Op) (st0) (V') (stObs) (o) : Prop | Observation.lean:39 |
| determinism | theorem RunCommitted.det, EVM.run_det; Determinism.lean is 432 lines | Observation.lean:45 |
| adequacy | Adequacy.lean, 791 lines; not yet read in detail | - |
| object run | def runObject (fuel : Nat) (o : Object EVM.Op) (L : Layout) | ObjectRun.lean:64 |
| printer | PrettyPrint.lean, 214 lines | - |

### Finding Y-1: ExternalCalls is a structure, so the plan's union does not typecheck

Plan 9.5 writes: def calls (L W) := Eip2537.rel union Modexp.rel union
Evaluator.rel L W. There is no union on ExternalCalls - it bundles one ternary
relation (CallRequest -> EvmState -> CallResponse -> Prop), with none and any
defaults at :532 and :535. The port must build a single ExternalCalls.mk whose
Call is a disjunction, and the three sub-relations must agree on any request two
of them match, or the disjunction is nondeterministic where the Rust is not.
Owner: Midfall/Yul/Bridge.

### Finding Y-2: the hash is an environment field, not a dialect parameter

keccak256 reads st.env.keccakOf (EVMExec.lean:731), where ExecEnv.keccakOf
defaults to opaque keccakBytes (:88, :158-160). So "the keccak256 oracle is H"
means installing an ExecEnv with keccakOf := H, not parameterising the dialect -
and the fork ships no executable keccak at all, so VCVio's must be wired in via
Common/Keccak.lean, exactly as plan Section 1 anticipates.

The trap: extcodehash is defined as keccakOf (extCodeOf address) (:298).
Installing H as the hash oracle therefore also defines extcodehash - which is
what makes Deployment.vkHash a statement about H - but it couples the shell
model to the hash. Any lowering_equivalence quantified over all H must define
vkCodehash and quotientCodehash as H of the code too, or the quantification is
vacuous for the hash-dependent parts. Owner: Phase 5, and a review of 9.5.

### Finding Y-3: RunCommitted is fixed to the closed EVM.evm dialect - BLOCKS M4

The plan writes EVM.RunCommitted (EVM.evmWithExternal (calls L W) noCreates)
(keccak := H) ... The actual RunCommitted (Observation.lean:39) takes no dialect
argument and no keccak named argument: it runs Run EVM.evm, the closed dialect.
So RunVerifier and RunContractIR as written do not typecheck. Two ways out, and
it is a decision: (a) define a Midfall-side open-dialect Run in Midfall/Yul/Bridge
and restate 9.5 against it - mechanical, but RunCommitted.det's functionality
argument leans on EVM.run_det, stated for the closed dialect, so it must be
reproved; or (b) upstream a dialect-parameterised RunCommitted to
powdr-labs/yul-semantics, which the plan already wants our additions to be.
Recommendation: (b), because (a) silently loses determinism. Owner: Phase 5,
before any verifier_sound work. This blocks M4.

### Finding Y-4: the object-level interpreter is fuel-bounded

runObject takes a fuel : Nat (ObjectRun.lean:64) and Interp.run too
(Interp.lean:212). The plan never mentions fuel, and 9.5's qvm_yul_refines and
RunContract (evaluatorObject L) statements are fuel-free. With a bound, "the
evaluator returns the encoded output or reverts" holds only above some fuel, so
either the theorems quantify over sufficient fuel or they use the unfuelled Run
relation Contract.lean builds on. The second is cleaner. Owner: Phase 5 / M6.

### Finding Y-5: gas can be pinned rather than left nondeterministic

ExternalGas (EVMExec.lean:549) has any (every read possible, what evmWithCalls
installs) and none (used at EVM.lean:263 to make gas() stuck). So the plan's
"gas() stays nondeterministic" is a choice: we could install an ExternalGas
returning exactly the scheduled constants curated item 4a made exact, turning
L2's "sufficient gas" hypothesis into a checkable equality. Exact gas is out of
scope by Section 1, so this is an option, not a task.

## 11. What `rust_trace.json` can and cannot drive (Phase 3 finding)

`proofs/solidity-verifier/fixtures/*/rust_trace.json` records, per event, the tag,
the 48-byte compressed point or the 32-byte big-endian scalar, and for squeezes the
**challenge value**. It is tempting to treat that as a replay script: absorb each
recorded item, squeeze at each recorded challenge, compare. That does not work, for
two independent reasons established by experiment on the poseidon fixture.

1. **The recorded challenges are reduced, the transcript reseeds on the raw**
   **digest.** `Transcript.squeeze` sets `state := digest`, while
   `squeezeChallenge` returns `digest mod r`. The trace stores the latter. All 10
   poseidon challenges are `< r`, where a raw digest would be below `r` with
   probability about 0.34 — so 10/10 is conclusive. Reduction mod `r` is not
   invertible, so the state cannot be reconstructed from the trace and no link in
   the chain can be seeded from it, including links that look local (beta depends on
   the raw digest behind theta, not on the recorded theta).
2. **The absorb prefix is not recorded at all.** Between `vk_repr` and the first
   read, `parse_trace` absorbs the committed instance commitments and, per instance
   column, the column length and its values. None of that appears in the trace. For
   poseidon the shape is known only from `zk_stdlib::verify`, which passes
   `&[committed_pi]` with `committed_pi = identity` when the caller supplies
   `None`, and `&[&pi]` with `pi = format_instance(instance)` whose length must
   equal `vk.nb_public_inputs` — a VK field the trace does not carry.

Consequence for the harness: a replay needs the digest stream, not the challenge
stream. Either the exporter records the raw digest at every squeeze, or the Lean
side must reproduce the whole chain from the VK and the instances — which is the
point of `verifyNative` in the first place. So the minimal `vk.json` is required,
but it is much smaller than plan Section 5's "full cs": to drive the transcript
replay one needs `nb_public_inputs`, the committed-instance count and values, the
instance column values, `cs_degree`, `k`, `omega`, and `transcript_repr`. The full
constraint system is only needed to reproduce the *evaluation* reads, which come
later and are already in the trace.

This is worth recording because it changes the exporter's cost: `ConstraintSystem`
has no serde derives, so emitting the "full cs" means hand-writing a serializer for
about twenty fields plus `Expression` trees inside `proofs/src` — a baseline bump.
The reduced schema above avoids that entirely.

### Status of the replay attempt (not yet achieved)

Correcting the reduction error above and re-running with `(keccak state) mod r`
compared against the recorded challenge, four candidate prefixes still fail to
reproduce poseidon's `theta`:

| prefix after `vk_repr` | result |
|---|---|
| nothing | no match |
| one instance column of length 1 | no match |
| committed identity (128 zero bytes) only | no match |
| committed identity + one instance column of length 1 | no match |

What is ruled out: the transcript primitives are not in question. The absorb
encoding, the decompression (blst-agreed on 21/21 points) and the squeeze reseed
were each validated independently earlier. What is NOT known is the instance shape:
`pi = format_instance(instance)` and `vk.nb_public_inputs` are not in the trace and
`instance.be` holds a single `to_repr`, which need not equal `pi`.

So the conclusion stands but is narrower than stated: the missing piece is the
instance/committed-instance shape, i.e. exactly the minimal `vk.json` fields. The
next step is to read `PoseidonExample::format_instance` (or dump `nb_public_inputs`
from the existing test) rather than to guess prefixes.

Process note worth keeping: this session produced two self-inflicted misdiagnoses in
a row - first comparing a raw digest against a reduced challenge, then calling that
probe 'prefix-independent' when it was not. Both were caught only by trying a check
whose expected outcome was uncertain enough to be informative. When a hypothesis
fails, verify the test can pass at all before believing the failure.

## 12. The vendored Yul AST cannot round-trip the generated Solidity (Phase 6 finding)

First measured against `deployments/sepolia/moonlight-wrap/Halo2Verifier.sol`
lines 199-220 and `vendor/yul-semantics/YulSemantics/{Ast,PrettyPrint}.lean`. The
construct table in 12.1 has since been re-anchored on the tracked fixture dump
(see the legend); the two structural reasons below hold for both files.

The vendored AST and printer are the right basis for **semantics** and must be
reused (D-P2 amendment). They cannot reproduce the **bytes** of the generated
contract, for two independent structural reasons:

1. **`Stmt Op` has no comment constructor.** The committed assembly is interleaved
   with `//` comments (deployed lines 200, 203-205, 210-211, 216-218; 1194 of the
   3024 lines of the dump begin with `//`). The AST cannot represent the file, so
   no printer over it can round-trip it.
2. **`ppStmt` always breaks blocks onto separate lines**
   (`PrettyPrint.lean:60-61`):

   ```lean
   | .block body =>
       "{\n" ++ ppStmts pOp (ind + 1) body ++ pad ind ++ "}"
   ```

   and likewise `.cond c body => "if " ++ ppExpr pOp c ++ " {\n" ++ ... `. An
   earlier revision of this section misquoted that line as
   `"{" ++ nl ++ ... ++ pad ind ++ ""}`, which is not what the vendored source
   says. The committed file uses single-line ifs such as
   `if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }`.

Comma spacing (", ") and the 4-space indent step do match.

**Consequence for plan Section 8.** Byte-identity of the generated Solidity is not a
property of the Yul AST alone. Comments and whitespace come from the Jinja
templates, so `render g o = (lower g o).map print` requires `lower` to emit an AST
**plus** a literal-text/comment stream, or `print` to be parameterised by the
template layout. Recording this before the printer was written, because the obvious
gate - parse the committed file, print it, compare - is not achievable and would have
been debugged for days.

**Consequence for plan Section 7.** `irCheck` compares embedded assembly blocks for
alpha-equivalence. That is the right notion - dropping comments is correct for
semantics - but it must not be conflated with byte-identity. The two checks are
different and both are needed: alpha-equivalence for `ir_refines`, byte-identity for
`deployed_equivalence`.

### 12.1 Construct-by-construct measurement (Phase 6 package 1)

Each row was produced by elaborating the committed bytes with the `yul%` DSL and
printing with `YulSemantics.EVM.print`, checked in
`Midfall/Generator/YulGolden.lean` (golden gates) and
`Midfall/Generator/Render.lean` (renderer notes).

**Legend.** `D:` = `proofs/solidity-verifier/target/poseidon-fixture-dump/Halo2Verifier.sol`
- the TRACKED DUMP produced by the current generator, 3024 lines, no trailing
newline. `DVK:` = `Halo2VerifyingKey.sol` in the same directory, 271 lines.
`P:` = `deployments/sepolia/moonlight-wrap/Halo2Verifier.sol`, the DEPLOYED
artifact, 3573 lines, generated 2026-05-19 by superseded templates. `QN` =
`templates/partials/quotient_numerator/QuotientNumeratorBlock.yul`.

R-38 found that this table used to say `V` while meaning `P`, and that
`Midfall/Generator/{Render,Filters}.lean` did the same: every `:NNNN` citation
pointed at the deployed artifact although the text claimed the dump, two of them
at lines past the end of the dump. Every row below has been re-read from the file
it now names. Where a construct exists only in the deployed artifact, the row says
so instead of citing a dump line that does not hold it.

| construct | committed bytes | vendored `EVM.print` | agree? |
|---|---|---|---|
| hex literal | `let scratch := 0x1000` (D:327) | `let scratch := 4096` | no - formatting |
| hex, zero | `add(p, 0x00)` (D:653) **and** `add(SELECTOR_ACC_MPTR, 0x0)` (D:1790) | `add(p, 0)` | no - see 12.2 |
| hex, 256 | `0x0100` (D:376) **and** `0x100` (D:472) | `256` | no - see 12.2 |
| `hex_padded(64)` word | `0x0000...0001` (DVK:69) | `1` | no - formatting |
| precompile address | `staticcall(G1ADD_GAS, 0x0b, ...)` (D:376) | `staticcall(G1ADD_GAS, 11, ...)` | no - formatting. The dump passes a NAMED gas constant; `gas()` occurs only in the deployed artifact (P:219) and nowhere in D |
| decimal literal | `shr(240, mload(q_pc))` (D:1905) | identical | **yes** |
| call spacing | `mcopy(add(scratch, 0x20), scratch, 0x20)` (D:333) | identical shape | **yes** |
| zero-arg call | `returndatasize()` (D:364), `q_program_fail()` (D:1911) | identical | **yes** |
| assignment | `inv := mload(p)` (D:661) | identical | **yes** |
| multi-name `let` | `let x_ok, x_hi, x_lo := load_acc_coord(...)` (D:1074) | identical | **yes** |
| multi-name assign | `hi, lo := load_acc_coord_shifted(...)` (D:1019) | identical | **yes** |
| indent step | 4 spaces (D:834 is level 5 at 20 spaces); zero tab characters in D | `pad n = 4*n` | **yes**, with the next row as the exception |
| indent is not a function of depth | D:1987-1993 puts a `for` body at the same indentation as its own `for` | always indents one level deeper | no - template layout, and it breaks the "4 spaces per level" rule as stated |
| one-statement `if` | inline (D:334) **and** multiline (D:378-380) | always multiline | no - formatting |
| empty block | `for {} ... {} {` (D:833) **and** `for { } ... { } {` (D:1894) | `for {` LF `}` | no - formatting |
| `for` header | inline (D:1509); the wrapped spelling is in the template (Lagrange.yul:30), not in D | always wrapped | no - formatting |
| spread call | one arg per line (D:399-408) | one line | no - formatting |
| `switch` arm indent | arms at the switch's own level (D:1902, D:1904) | same | **yes** |
| `case` label | `case 0x05 {` (D:1904) | `case 5 {` | no - formatting |
| `leave` | bare (D:783) | bare | **yes** |
| `break` / `continue` | do not occur anywhere in D | bare | untested by the corpus; the renderer's spelling is a choice, not a measurement |
| whole-line comment | 1194 of D's 3024 lines (`grep -cE '^[[:space:]]*//'`); 1204 lines contain `//` | **no AST node exists** | not representable |
| trailing comment | `mstore(add(scratch, 0x00), 0x20)        // base len` (D:357) | not representable | not representable |
| text after a closing brace | `}            // ===` - **deployed only** (P:1413). No line of D has `}` followed by a comment | not representable | not representable |
| blank lines | 122 in D, SIX of which carry indentation (D:85, 525, 1098, 1103, 1891, 3010) | none emitted | not representable |
| comment INSIDE one statement | D:1902-1904 is `switch q_op` / comment / `case 0x05 {` - all one `Stmt.switch`; D:1020-1025 is a statement `ok := and(` whose comment lines (D:1022-1023) sit between its arguments | no AST node, and `Render.lean`'s `Line.tail` can only extend the CURRENT line or start a new one, never interrupt a statement that is still open | not representable - the fourth divergence, found by the R-38 review |
| free identifiers | `FR_MODULUS`, `MODEXP_GAS`, `ERR_NON_CANONICAL_SCALAR` and 91 `uint256 internal constant` declarations in D | compared as unbound name strings | representable, but the spelling is decided OUTSIDE the Yul - see 12.4 |

The two figures an earlier revision of this table gave - "971 comment lines" and
"99 blank lines" in `V` - are not reproducible against either artifact and have
been replaced with the measured counts and the commands that produce them.


### 12.2 Two findings that survive the D-P13 relaxation

* **The literal-spelling collision is not a formatting choice.** The committed file
  spells 0 as both `0x00` (D:653) and `0x0` (D:1790), and 256 as both `0x0100`
  (D:376) and `0x100` (D:472). All four elaborate to the same `Literal.number`, so
  **no function from the vendored AST can reproduce the bytes** - not because
  formatting is excluded by D-P13, but because two distinct committed texts share
  one AST. Harmless for correctness under D-P13; fatal for the original
  "byte for byte" phrasing of `deployed_equivalence`, which now needs either a
  spelling channel on `Literal` (upstream) or an explicit statement that
  byte-identity is a property of the template output stream and not of the AST.
  Owner: whoever restates plan 9.6.
* **Identifier equality is string equality, so alpha-renaming is NOT quotiented.**
  `SyntaxEq.stmtsBeq` compares binder and callee names with `==`, and
  `YulGolden.discriminates_ident_ok` pins that `let scratch := 0x80` and
  `let other := 0x80` are unequal. On the Rust side the positional names come from
  a counter (`next_var`, `format!("var{count}")`, yul_emit.rs:1140-1143) and the
  expression-to-name cache is only ever `contains_key` / index / insert, never
  iterated (yul_emit.rs:64, 1130-1134), so no HashMap ordering can leak into a
  name. The port must nevertheless reproduce the counter's *emission order*, which
  is a real obligation - and structural equality catches a miss, loudly. Owner:
  Phase 6 `QuotientNumerator/YulEmit`.

### 12.3 What the M3 golden test is now

`Midfall/Generator/YulGolden.lean`: **eight** slices transcribed from the
committed bytes into `yul%` quotations. Each slice now carries three
independently-checked sides.

1. **Authoritative (D-P13).** `<base>_ast` is compared with `<base>_direct`,
   the same slice written with raw AST constructors, using
   `YulSemantics.SyntaxEq.stmtsBeq` - the relation Phase 5's `irCheck` will
   use. Eight `<base>_beq_ok` gates plus `golden_beq_all_ok`.
2. **Secondary.** `EVM.print` of the AST is compared as a **token stream** with
   the pinned string: comments dropped, whitespace dropped, every numeric literal
   reduced to its value. Eight `<base>_golden_ok` gates plus `golden_all_ok`.
3. **Provenance.** `scripts/check_golden_provenance.py` re-reads each cited line
   range from the tracked `.sol`, re-tokenises it with the same rules, and
   asserts the pinned string, the line/byte/token counts and the sha256. It runs
   from `scripts/checks.sh`.

**The claim an earlier revision made is false and is withdrawn.** The token relation
is NOT the D-P13 equality and is NOT "the same structural equality Phase 5's
`irCheck` will use": it is strictly weaker. `PrettyPrint.lean:44-45` prints
`Expr.builtin` and `Expr.call` identically while `Ast.lean:109-113` keeps
the constructors distinct, so a port that emits `.call "add"` where the Rust
means the built-in passes every token gate and is rejected by `irCheck`.
`YulGolden.discriminates_builtinVsCall_ok` pins that asymmetry: the two trees are
unequal under `stmtsBeq` and equal under the token relation. M3 and Phase 5 share
one AST type; they now share one equality only via the `_beq_ok` gates, not via
the token gates.

Discrimination gates show both relations can fail on a minimal perturbation of a
REAL fixture: one literal value changed (`discriminates_fixture_ok`), one
identifier renamed (`discriminates_fixtureIdent_ok`), a built-in collapsed to a
user call (`discriminates_builtinVsCall_ok`), plus the toy-shape gates for
identifier spelling, argument order, literal value, statement shape and multi-name
`let`.
Each was falsified by removing the perturbation and watching exactly one gate go
red; the previous `discriminates_fixture_ok` compared a one-statement block
against a twenty-four-statement fixture and was true with no perturbation at all
(R-38 finding 4).

### 12.4 Two divergences the R-38 review added, both of which bite Phase 5

* **A comment can sit inside a single statement.** D:1902-1904 is `switch q_op`
  on one line, a `//` comment on the next, and `case 0x05 {` on the third -
  all of it ONE `Stmt.switch`, because the case list is part of that statement.
  the statement D:1020-1025 is the same shape inside an expression: `ok := and(`
  spread over six lines, with two comment lines (D:1022-1023) sitting between its
  two arguments. Neither the AST (no
  comment constructor) nor `Render.lean`'s `Line` stream can carry it:
  `Line.tail` extends the CURRENT line and `Line.text` starts a new one, so
  there is no way to say "emit this text in the middle of a statement that is
  still open". A renderer that must reproduce D byte-for-byte needs either a
  pre-opened-statement text channel or a statement printer that takes an
  interleaved comment list. Phase 6 owes that decision before `deployed_equivalence`
  can be stated at all.
* **The fixtures contain free identifiers.** `FR_MODULUS`, `MODEXP_GAS`,
  `G1ADD_GAS`, `ERR_NON_CANONICAL_SCALAR` and the rest are not defined in
  the Yul: they are 91 `uint256 internal constant` declarations in the enclosing
  Solidity (measured: `grep -c 'internal constant'` over D). `stmtsBeq`
  compares them as unbound name strings, so two generators can agree on every
  `Stmt` and still disagree on the emitted file if they bind the name to a
  different value or spell it differently - and the equality relation has no way
  to see it. Phase 5's `irCheck` therefore cannot be the only check on the
  constant table: the Solidity-level constants need their own known-answer test
  against the artifact. Owner: Phase 5, with Phase 6's `Filters.lean` as the
  model for how a spelling decision gets pinned.

## 13. Is the fixture dump current with this branch's sources? (Phase 6 provenance)

Asked directly while porting the template layer, because R-36 had just shown the
deployed artifact was five months stale. Answer: **yes, verified three ways** - with
one residual hole worth closing.

1. `target/poseidon-fixture-dump/Halo2Verifier.sol` was last committed at `5312cb7`
   (2026-10-23), which is an ancestor of HEAD, and **zero commits touch `src/` or
   `templates/` after it**. So the dump is not stale relative to committed sources.
2. `cargo test -p halo2_solidity_verifier --test template_digest` **passes**. That
   test exists precisely for this hazard - its header says committed replay fixtures
   compile pre-rendered `.sol`, so "a template edit whose fixtures were not
   regenerated keeps every replay test green while the deployable artifacts silently
   drift" - and it pins a keccak over the whole `templates/` tree.
3. The only uncommitted Rust change on the branch is `api.rs` adding
   `RenderedArtifacts::named_bytes()`, a getter returning the renderer's existing
   output under stable filenames. It does not change rendering.

**Residual hole.** The digest covers `templates/` only, not `src/`, so a change to the
renderer logic in `src/lowering/render/*.rs` is not caught by it - leg 1 covers that
for committed history but not for working-tree edits. More importantly the guarantee
is weaker than it looks: the pin and the dump are updated by hand independently. If
someone edits a template, regenerates the dump, and forgets to re-pin, the test fails
(good). If they edit a template, re-pin, and do **not** regenerate the dump, the test
passes while the dump is stale (bad). The claim "the dumps were regenerated before
this value was recorded" lives in a comment, not in a check.

**Cheap fix, not yet done.** Have the fixture tests write a sidecar (or a header line)
recording the template-tree digest they used, so dump-to-templates is machine-checked
rather than asserted. That closes the loop for the price of a few lines in the test
harness and no change to `proofs/src`.

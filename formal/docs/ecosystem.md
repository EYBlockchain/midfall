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

Action: revisit as its own work package (nice-to-have, not on the M1 or M0 path).
The cheaper non-vacuity argument is that AdmissiblePairing is a *signature*
constraint, not an existence claim: the statements are implications, and the
concrete instance arrives with Assumptions/Pairing.lean.

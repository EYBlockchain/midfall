// SPDX-License-Identifier: CC0-1.0
//! EVM-enabled integration-style tests for rendered Solidity verifier behavior.
//!
//! This module is compiled only for crate tests with the `evm` feature. It
//! exercises compiled verifier contracts, calldata encoding, proof repacking,
//! and runtime failure modes that cannot be covered by pure codegen unit tests.

#[cfg(feature = "rust-verifier-trace")]
use std::collections::BTreeMap;
use std::{
    env,
    panic::AssertUnwindSafe,
    path::{Path, PathBuf},
    sync::OnceLock,
};

use ff::Field;
use group::{Curve as _, Group as _};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{hash::HashCPU, AssignmentInstructions, PublicInputInstructions},
};
use midnight_curves::{Bls12, Fq, G1Projective, G2Projective};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk_with_k, prepare, Advice, Circuit, Column,
        ConstraintSystem, Constraints, Error, Expression, Fixed, SecondPhase, Selector,
    },
    poly::{commitment::Guard as _, kzg::KZGCommitmentScheme, Rotation},
    transcript::{CircuitTranscript, Transcript},
};
#[cfg(not(feature = "outer-single-h-commitment"))]
use midnight_zk_stdlib::utils::plonk_api::srs_for_test;
#[cfg(feature = "outer-single-h-commitment")]
use midnight_zk_stdlib::{
    cost_model,
    utils::plonk_api::{load_srs, SrsSource},
};
use midnight_zk_stdlib::{setup_vk, MidnightVK, Relation, ZkStdLib, ZkStdLibArch};
use proptest::{
    prelude::any,
    test_runner::{Config as ProptestConfig, TestRunner},
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
#[cfg(feature = "rust-verifier-trace")]
use revm::primitives::B256;
use ruint::aliases::U256;
use sha3::Digest;

use crate::{
    compile_solidity, compile_solidity_runtime, encode_calldata, pinned_solc_available,
    runtime_free_memory_pointer_init, AccumulatorEncoding, CallOutcome, Evm, GeneratorConfig,
    RenderDiagnostics, RenderOptions, RenderQuotient, RenderVk, SolidityGenerator,
    FN_SIG_VERIFY_PROOF,
};

/// Scalar field used by the BLS12-381 Poseidon fixtures.
type F = midnight_curves::Fq;
/// KZG parameters type used by Poseidon fixture generation.
type PoseidonParams = midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>;
/// Verifier-only KZG parameters type used for native verification checks.
type PoseidonVerifierParams =
    midnight_proofs::poly::kzg::params::ParamsVerifierKZG<midnight_curves::Bls12>;

/// Small fixture domain size for Poseidon verifier tests.
const POSEIDON_K: u32 = 6;
/// Environment flag that opts into expensive EVM/Solidity integration tests.
const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";
/// Source for the test SRS, as documented by `zk_stdlib`'s own loader error.
const SRS_DOWNLOAD_URL: &str =
    "https://midnight-s3-fileshare-dev-eu-west-1.s3.eu-west-1.amazonaws.com/bls_filecoin_2p19";
/// Minimal caller used to exercise the production verifier under STATICCALL.
const STATICCALL_VERIFIER_HARNESS: &str = r#"
// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.24;

contract StaticcallVerifierHarness {
    address immutable verifier;

    constructor(address verifier_) {
        verifier = verifier_;
    }

    function check(bytes calldata verifyCalldata) external view returns (bool) {
        (bool ok, bytes memory output) = verifier.staticcall(verifyCalldata);
        if (!ok || output.length != 32) {
            return false;
        }
        return abi.decode(output, (bool));
    }
}
"#;

#[test]
fn function_signature() {
    assert_eq!(
        <[u8; 32]>::from(sha3::Keccak256::digest("verifyProof(bytes,uint256[])"))[..4],
        FN_SIG_VERIFY_PROOF,
    );
}

/// Direct EIP-2537 precompile conformance tests against the bundled
/// Prague-spec revm. Exercises the runner path independently of the verifier
/// codegen so a regression in `src/evm.rs`, malformed-point handling, or the
/// gas path used by large verifier MSMs shows up here first.
#[test]
fn prague_evm_runs_eip2537_conformance_smoke_tests() {
    use revm::primitives::Address;

    use crate::evm::test::Evm;

    let mut evm = Evm::default();

    let g1add = Address::with_last_byte(0x0b);
    let g1msm = Address::with_last_byte(0x0c);
    let pairing = Address::with_last_byte(0x0f);
    let g1 = G1Projective::generator();
    let g2 = G2Projective::generator();

    // G1ADD(identity, identity) -> identity.
    let (_gas_used, output) = evm.call(g1add, vec![0; 0x100]);
    assert_eq!(output, vec![0; 0x80]);

    // G1ADD(G, G) -> 2G.
    let mut g1add_input = g1_bytes(g1);
    g1add_input.extend(g1_bytes(g1));
    let (_gas_used, output) = evm.call(g1add, g1add_input);
    assert_eq!(output, g1_bytes(g1 * Fq::from(2)));

    // G1MSM([(identity, 0)]) -> identity.
    let (_gas_used, output) = evm.call(g1msm, vec![0; 0xa0]);
    assert_eq!(output, vec![0; 0x80]);

    // G1MSM([(G, 3), ([2]G, 5)]) -> [13]G.
    let mut g1msm_input = g1_msm_term(g1, 3);
    g1msm_input.extend(g1_msm_term(g1 * Fq::from(2), 5));
    let (_gas_used, output) = evm.call(g1msm, g1msm_input);
    assert_eq!(output, g1_bytes(g1 * Fq::from(13)));

    // Malformed/off-curve G1 input must be rejected by the MSM precompile.
    let mut invalid_msm = eip2537_padded_off_curve_g1_bytes().to_vec();
    invalid_msm.extend(u256_word(1));
    assert!(
        !matches!(
            evm.try_call_with_gas(g1msm, invalid_msm, 200_000),
            CallOutcome::Success { .. }
        ),
        "G1MSM accepted a canonical but off-curve G1 point"
    );

    // Full-size 78-term MSM path used by wide verifier shapes. The exact gas
    // number is fork-dependent; this asserts the local Prague runner has a
    // conforming large-input path and returns a non-identity point.
    let mut large_msm = Vec::with_capacity(78 * 0xa0);
    for _ in 0..78 {
        large_msm.extend(g1_msm_term(g1, 1));
    }
    match evm.try_call_with_gas(g1msm, large_msm, 2_000_000) {
        CallOutcome::Success { output, .. } => {
            assert_eq!(output.len(), 0x80);
            assert!(
                output.iter().any(|&b| b != 0),
                "78-term G1MSM unexpectedly returned identity"
            );
        }
        outcome => panic!("78-term G1MSM failed in Prague revm: {outcome:?}"),
    }

    // Pairing identity input should return true.
    let (_gas_used, output) = evm.call(pairing, vec![0; 0x180]);
    assert_eq!(output, [vec![0; 31], vec![1]].concat());

    // A single non-identity generator pairing is not the neutral product.
    let mut invalid_pairing = g1_bytes(g1);
    invalid_pairing.extend(g2_bytes(g2));
    let (_gas_used, output) = evm.call(pairing, invalid_pairing);
    assert_eq!(
        output,
        vec![0; 0x20],
        "PAIRING_CHECK([(G1, G2)]) should return false"
    );

    // Bilinearity: e([2]G1, G2) * e(-G1, [2]G2) == 1.
    let mut bilinear_pairing = g1_bytes(g1 * Fq::from(2));
    bilinear_pairing.extend(g2_bytes(g2));
    bilinear_pairing.extend(g1_bytes(-g1));
    bilinear_pairing.extend(g2_bytes(g2 * Fq::from(2)));
    let (_gas_used, output) = evm.call(pairing, bilinear_pairing);
    assert_eq!(output, [vec![0; 31], vec![1]].concat());
}

/// Encode a G1 point in the padded EIP-2537 byte layout.
fn g1_bytes(point: G1Projective) -> Vec<u8> {
    words_to_bytes(crate::__test_only_g1_to_u256s(&point.to_affine()))
}

/// Encode a G2 point in the padded EIP-2537 byte layout.
fn g2_bytes(point: G2Projective) -> Vec<u8> {
    words_to_bytes(crate::__test_only_g2_to_u256s(&point.to_affine()))
}

/// Build one `(G1, scalar)` input tuple for the G1MSM precompile.
fn g1_msm_term(point: G1Projective, scalar: u64) -> Vec<u8> {
    let mut out = g1_bytes(point);
    out.extend(u256_word(scalar));
    out
}

/// Encode a small integer as one big-endian EVM word.
fn u256_word(value: u64) -> [u8; 32] {
    U256::from(value).to_be_bytes()
}

/// Flatten U256 words into big-endian bytes.
fn words_to_bytes<const N: usize>(words: [U256; N]) -> Vec<u8> {
    words.into_iter().flat_map(|word| word.to_be_bytes::<32>()).collect()
}

#[derive(Clone, Copy, Debug, Default)]
struct ShapeFuzzSpec {
    next_rotation: bool,
    second_phase: bool,
    permutation: bool,
    lookup: bool,
    additive_selector: bool,
    complex_selector: bool,
    fixed_scale: bool,
    tag: u64,
}

#[derive(Clone, Copy, Debug)]
struct ShapeFuzzCase {
    name: &'static str,
    k: u32,
    spec: ShapeFuzzSpec,
    seed: u64,
}

#[derive(Clone, Debug)]
struct ShapeFuzzConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    out: Column<Advice>,
    phase2: Option<Column<Advice>>,
    fixed_scale: Option<Column<Fixed>>,
    lookup_table: Option<Column<Fixed>>,
    selector: Selector,
}

#[derive(Clone, Debug)]
struct ShapeFuzzCircuit {
    spec: ShapeFuzzSpec,
    a: F,
    b: F,
}

impl ShapeFuzzCircuit {
    /// Deterministically construct a shape-fuzz witness.
    fn new(spec: ShapeFuzzSpec, seed: u64) -> Self {
        let a = F::from(seed.wrapping_mul(17).wrapping_add(5));
        let b = F::from(seed.wrapping_mul(29).wrapping_add(11));
        Self { spec, a, b }
    }

    /// Advice output constrained by the synthetic circuit.
    fn out(&self) -> F {
        self.a + self.b + F::from(self.spec.tag + 19)
    }

    /// Public input derived from the output and advice values.
    fn public_instance(&self) -> F {
        self.out() - self.a - self.b
    }

    /// Next-row advice value used when the shape enables rotations.
    fn next_a(&self) -> F {
        self.a + F::from(self.spec.tag + 7)
    }

    /// Second-phase advice value used when the shape enables phase two.
    fn phase2_value(&self) -> F {
        self.out() + F::from(self.spec.tag + 23)
    }
}

impl Circuit<F> for ShapeFuzzCircuit {
    /// Config columns for the generated shape-fuzz circuit.
    type Config = ShapeFuzzConfig;
    /// Simple floor planner is enough for these synthetic fixtures.
    type FloorPlanner = SimpleFloorPlanner;
    /// Shape parameters are supplied through Halo2's parameterized configure.
    type Params = ShapeFuzzSpec;

    /// Return the circuit shape without witness values.
    fn without_witnesses(&self) -> Self {
        Self {
            spec: self.spec,
            a: F::ZERO,
            b: F::ZERO,
        }
    }

    /// Return the shape parameters used during configuration.
    fn params(&self) -> Self::Params {
        self.spec
    }

    /// The non-parameterized configure path is intentionally disabled.
    fn configure(_meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!("ShapeFuzzCircuit is always configured with explicit params")
    }

    /// Configure a synthetic circuit with optional features toggled by `spec`.
    fn configure_with_params(meta: &mut ConstraintSystem<F>, spec: Self::Params) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let out = meta.advice_column();
        let phase2 = spec.second_phase.then(|| meta.advice_column_in(SecondPhase));
        let fixed_scale = spec.fixed_scale.then(|| meta.fixed_column());
        let lookup_table = spec.lookup.then(|| meta.fixed_column());
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();

        if spec.permutation {
            for column in [a, b, out] {
                meta.enable_equality(column);
            }
        }

        let selector = if spec.additive_selector || spec.complex_selector || spec.lookup {
            meta.complex_selector()
        } else {
            meta.selector()
        };

        meta.create_gate("shape-fuzz arithmetic", |meta| {
            let a_cur = meta.query_advice(a, Rotation::cur());
            let b_cur = meta.query_advice(b, Rotation::cur());
            let out_cur = meta.query_advice(out, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());

            let mut balance = a_cur.clone() + b_cur + public + committed - out_cur.clone();
            if let Some(scale) = fixed_scale {
                balance = meta.query_fixed(scale, Rotation::cur()) * balance;
            }

            let mut constraints = vec![("public balance", balance)];
            if spec.next_rotation {
                constraints.push((
                    "next rotation",
                    meta.query_advice(a, Rotation::next())
                        - a_cur
                        - Expression::Constant(F::from(spec.tag + 7)),
                ));
            }
            if let Some(phase2) = phase2 {
                constraints.push((
                    "second phase",
                    meta.query_advice(phase2, Rotation::cur())
                        - out_cur
                        - Expression::Constant(F::from(spec.tag + 23)),
                ));
            }

            if spec.additive_selector {
                Constraints::with_additive_selector(selector, constraints)
            } else {
                Constraints::with_selector(selector, constraints)
            }
        });

        if let Some(table) = lookup_table {
            meta.lookup_any("shape-fuzz lookup", Some(selector), |meta| {
                vec![(
                    meta.query_advice(a, Rotation::cur()),
                    meta.query_fixed(table, Rotation::cur()),
                )]
            });
        }

        ShapeFuzzConfig {
            a,
            b,
            out,
            phase2,
            fixed_scale,
            lookup_table,
            selector,
        }
    }

    /// Assign witness rows and optional lookup/permutation/phase-two cells.
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "shape-fuzz witness",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", config.a, 0, || Value::known(self.a))?;
                region.assign_advice(|| "b", config.b, 0, || Value::known(self.b))?;
                region.assign_advice(|| "out", config.out, 0, || Value::known(self.out()))?;

                if self.spec.next_rotation {
                    region.assign_advice(
                        || "a next",
                        config.a,
                        1,
                        || Value::known(self.next_a()),
                    )?;
                }
                if let Some(column) = config.phase2 {
                    region.assign_advice(
                        || "second phase value",
                        column,
                        0,
                        || Value::known(self.phase2_value()),
                    )?;
                }
                if let Some(column) = config.fixed_scale {
                    region.assign_fixed(|| "fixed scale", column, 0, || Value::known(F::ONE))?;
                }
                if let Some(column) = config.lookup_table {
                    region.assign_fixed(
                        || "lookup table value",
                        column,
                        0,
                        || Value::known(self.a),
                    )?;
                }

                if self.spec.permutation {
                    let copied = region.assign_advice(
                        || "permutation source",
                        config.a,
                        2,
                        || Value::known(self.b),
                    )?;
                    copied.copy_advice(|| "permutation target", &mut region, config.b, 3)?;
                }

                Ok(())
            },
        )
    }
}

#[test]
fn lookup_shape_verifier_compiles_with_native_lookup_callback() {
    if !shape_fuzz_inputs_available_for_evm() {
        return;
    }

    let case = ShapeFuzzCase {
        name: "native lookup compile",
        k: 5,
        seed: 303,
        spec: ShapeFuzzSpec {
            second_phase: true,
            lookup: true,
            fixed_scale: true,
            tag: 3,
            ..ShapeFuzzSpec::default()
        },
    };
    let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
    let mut setup_rng = ChaCha8Rng::seed_from_u64(case.seed ^ 0x5eed_5eed);
    let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
    let vk = keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` vk generation failed: {err:?}", case.name));

    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .unwrap_or_else(|err| panic!("shape fuzz `{}` render failed: {err:?}", case.name));
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");

    assert!(
        verifier_solidity.contains("case 0x1f"),
        "lookup verifier should include the native lookup VM callback"
    );
    assert!(
        verifier_solidity.contains("q_lookup_f"),
        "lookup verifier should include the structured lookup callback body"
    );

    assert!(!compile_solidity(verifier_solidity).is_empty());
    assert!(!compile_solidity(vk_solidity).is_empty());
}

#[test]
fn supported_shape_circuit_fuzz_e2e() {
    if !shape_fuzz_inputs_available_for_evm() {
        return;
    }

    let cases = supported_shape_evm_cases();

    let requested = env::var("SHAPE_FUZZ_CASES")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(cases.len())
        .min(cases.len());

    #[cfg(feature = "rust-verifier-trace")]
    let mut compared_selector_folds = false;
    for case in cases.iter().take(requested) {
        let case_compared_selector_folds = run_supported_shape_fuzz_case(case);
        #[cfg(feature = "rust-verifier-trace")]
        {
            compared_selector_folds |= case_compared_selector_folds;
        }
        #[cfg(not(feature = "rust-verifier-trace"))]
        {
            let _ = case_compared_selector_folds;
        }
    }

    #[cfg(feature = "rust-verifier-trace")]
    if requested > 0 {
        assert!(
            compared_selector_folds,
            "shape fuzz trace suite should include at least one selector-fold comparison"
        );
    }
}

fn supported_shape_evm_cases() -> [ShapeFuzzCase; 7] {
    [
        ShapeFuzzCase {
            name: "simple-selector current-row fixed-scale",
            k: 5,
            seed: 101,
            spec: ShapeFuzzSpec {
                fixed_scale: true,
                tag: 1,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "next-rotation permutation",
            k: 5,
            seed: 202,
            spec: ShapeFuzzSpec {
                next_rotation: true,
                permutation: true,
                tag: 2,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "second-phase lookup",
            k: 5,
            seed: 303,
            spec: ShapeFuzzSpec {
                second_phase: true,
                lookup: true,
                fixed_scale: true,
                tag: 3,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "trash-additive selector with lookup",
            k: 5,
            seed: 404,
            spec: ShapeFuzzSpec {
                next_rotation: true,
                lookup: true,
                additive_selector: true,
                fixed_scale: true,
                tag: 4,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "complex-selector second-phase permutation",
            k: 5,
            seed: 505,
            spec: ShapeFuzzSpec {
                second_phase: true,
                permutation: true,
                complex_selector: true,
                fixed_scale: true,
                tag: 5,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "additive-selector phase2 permutation",
            k: 5,
            seed: 606,
            spec: ShapeFuzzSpec {
                second_phase: true,
                permutation: true,
                additive_selector: true,
                tag: 6,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "full mixed lookup permutation shape",
            k: 5,
            seed: 707,
            spec: ShapeFuzzSpec {
                next_rotation: true,
                second_phase: true,
                permutation: true,
                lookup: true,
                complex_selector: true,
                fixed_scale: true,
                tag: 7,
                ..ShapeFuzzSpec::default()
            },
        },
    ]
}

#[test]
fn same_srs_distinct_shape_matrix_rejects_cross_wiring() {
    if !shape_fuzz_inputs_available_for_evm() {
        return;
    }

    let cases = [
        supported_shape_evm_cases()[0],
        supported_shape_evm_cases()[2],
        supported_shape_evm_cases()[4],
        supported_shape_evm_cases()[6],
    ];

    let mut setup_rng = ChaCha8Rng::seed_from_u64(0x5a5a_5151);
    let shapes: Vec<_> = cases.iter().map(|case| (case.spec, case.k)).collect();
    let params = shape_fuzz_params(&shapes, &mut setup_rng);
    let fixtures: Vec<_> = cases
        .iter()
        .map(|case| build_shape_solidity_case_with_params(&params, case))
        .collect();

    for left in 0..fixtures.len() {
        for right in (left + 1)..fixtures.len() {
            assert_ne!(
                fixtures[left].verifier_solidity, fixtures[right].verifier_solidity,
                "different circuit shapes over the same SRS should not share verifier source: {} vs {}",
                fixtures[left].name, fixtures[right].name
            );
            assert_ne!(
                fixtures[left].vk_solidity, fixtures[right].vk_solidity,
                "different circuit shapes over the same SRS should not share VK source: {} vs {}",
                fixtures[left].name, fixtures[right].name
            );
        }
    }

    for verifier_idx in 0..fixtures.len() {
        for vk_idx in 0..fixtures.len() {
            if verifier_idx == vk_idx {
                continue;
            }
            assert_separate_verifier_rejects_vk_dependency(
                &fixtures[verifier_idx].verifier_solidity,
                &fixtures[vk_idx].vk_solidity,
                &format!(
                    "{} verifier with {} VK",
                    fixtures[verifier_idx].name, fixtures[vk_idx].name
                ),
            );
        }
    }

    let mut deployed: Vec<_> = fixtures
        .iter()
        .map(|fixture| {
            deploy_separate_verifier_from_sources(&fixture.verifier_solidity, &fixture.vk_solidity)
        })
        .collect();

    for (idx, fixture) in fixtures.iter().enumerate() {
        assert_solidity_accepts(
            call_deployed_verifier(&mut deployed[idx], &fixture.proof, &fixture.public),
            &format!("same-SRS {} valid proof", fixture.name),
        );
    }

    for verifier_idx in 0..deployed.len() {
        for proof_idx in 0..fixtures.len() {
            if verifier_idx == proof_idx {
                continue;
            }
            assert_solidity_rejects(
                call_deployed_verifier(
                    &mut deployed[verifier_idx],
                    &fixtures[proof_idx].proof,
                    &fixtures[proof_idx].public,
                ),
                &format!(
                    "{} proof under {} verifier",
                    fixtures[proof_idx].name, fixtures[verifier_idx].name
                ),
            );
        }
    }
}

#[cfg(feature = "rust-verifier-trace")]
#[test]
fn pbt_transcript_differential_fuzzer_matches_solidity_trace() {
    if !shape_fuzz_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_transcript_differential_shape_fuzz_case(seed);
            Ok(())
        })
        .unwrap();
}

#[derive(Debug)]
struct ShapeSolidityCase {
    name: &'static str,
    verifier_solidity: String,
    vk_solidity: String,
    proof: Vec<u8>,
    public: Vec<F>,
}

fn build_shape_solidity_case_with_params(
    params: &PoseidonParams,
    case: &ShapeFuzzCase,
) -> ShapeSolidityCase {
    let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
    let vk = keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(params, &circuit, case.k)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` vk generation failed: {err:?}", case.name));
    let pk = keygen_pk(vk, &circuit)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` pk generation failed: {err:?}", case.name));

    let committed = [F::ZERO];
    let public = [circuit.public_instance()];
    let all_instance_columns: [&[F]; 2] = [&committed, &public];
    let mut proof_rng = ChaCha8Rng::seed_from_u64(case.seed ^ 0x0bad_f00d);
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init();
    create_proof::<F, KZGCommitmentScheme<Bls12>, _, _>(
        params,
        &pk,
        std::slice::from_ref(&circuit),
        1,
        &[&all_instance_columns],
        &mut proof_rng,
        &mut transcript,
    )
    .unwrap_or_else(|err| {
        panic!(
            "shape fuzz `{}` proof generation failed: {err:?}",
            case.name
        )
    });
    let compressed_proof = transcript.finalize();

    let committed_pi = [G1Projective::identity()];
    let public_columns: [&[F]; 1] = [&public];
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init_from_bytes(&compressed_proof);
    let guard = prepare::<F, KZGCommitmentScheme<Bls12>, CircuitTranscript<sha3::Keccak256>>(
        pk.get_vk(),
        &[&committed_pi],
        &[&public_columns],
        &mut transcript,
    )
    .unwrap_or_else(|err| panic!("shape fuzz `{}` native prepare failed: {err:?}", case.name));
    transcript.assert_empty().unwrap_or_else(|_| {
        panic!(
            "shape fuzz `{}` native transcript had trailing bytes",
            case.name
        )
    });
    guard
        .verify(&params.verifier_params())
        .unwrap_or_else(|err| panic!("shape fuzz `{}` native verify failed: {err:?}", case.name));

    let generator =
        SolidityGenerator::new(params, pk.get_vk(), GeneratorConfig::new(public.len(), 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .unwrap_or_else(|err| panic!("shape fuzz `{}` render failed: {err:?}", case.name));
    let proof = generator
        .repack_proof(&compressed_proof)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` repack failed: {err:?}", case.name));

    ShapeSolidityCase {
        name: case.name,
        verifier_solidity: artifacts.verifier,
        vk_solidity: artifacts.verifying_key.expect("separate render includes VK"),
        proof,
        public: public.to_vec(),
    }
}

/// Render, deploy, and exercise one supported shape-fuzz case end to end.
fn run_supported_shape_fuzz_case(case: &ShapeFuzzCase) -> bool {
    let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
    let mut setup_rng = ChaCha8Rng::seed_from_u64(case.seed ^ 0x5eed_5eed);
    let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
    let vk = keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` vk generation failed: {err:?}", case.name));
    let pk = keygen_pk(vk, &circuit)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` pk generation failed: {err:?}", case.name));

    let committed = [F::ZERO];
    let public = [circuit.public_instance()];
    let all_instance_columns: [&[F]; 2] = [&committed, &public];
    let mut proof_rng = ChaCha8Rng::seed_from_u64(case.seed ^ 0x0bad_f00d);
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init();
    create_proof::<F, KZGCommitmentScheme<Bls12>, _, _>(
        &params,
        &pk,
        std::slice::from_ref(&circuit),
        1,
        &[&all_instance_columns],
        &mut proof_rng,
        &mut transcript,
    )
    .unwrap_or_else(|err| {
        panic!(
            "shape fuzz `{}` proof generation failed: {err:?}",
            case.name
        )
    });
    let compressed_proof = transcript.finalize();

    let committed_pi = [G1Projective::identity()];
    let public_columns: [&[F]; 1] = [&public];
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init_from_bytes(&compressed_proof);
    let guard = prepare::<F, KZGCommitmentScheme<Bls12>, CircuitTranscript<sha3::Keccak256>>(
        pk.get_vk(),
        &[&committed_pi],
        &[&public_columns],
        &mut transcript,
    )
    .unwrap_or_else(|err| panic!("shape fuzz `{}` native prepare failed: {err:?}", case.name));
    transcript.assert_empty().unwrap_or_else(|_| {
        panic!(
            "shape fuzz `{}` native transcript had trailing bytes",
            case.name
        )
    });
    guard
        .verify(&params.verifier_params())
        .unwrap_or_else(|err| panic!("shape fuzz `{}` native verify failed: {err:?}", case.name));

    let generator =
        SolidityGenerator::new(&params, pk.get_vk(), GeneratorConfig::new(public.len(), 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .unwrap_or_else(|err| panic!("shape fuzz `{}` render failed: {err:?}", case.name));
    let verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");
    let repacked_proof = generator
        .repack_proof(&compressed_proof)
        .unwrap_or_else(|err| panic!("shape fuzz `{}` repack failed: {err:?}", case.name));
    let mut deployed = deploy_separate_verifier_from_sources(&verifier_solidity, &vk_solidity);

    assert_solidity_accepts(
        call_deployed_verifier(&mut deployed, &repacked_proof, &public),
        &format!("shape fuzz `{}` valid proof", case.name),
    );

    #[cfg(feature = "rust-verifier-trace")]
    let compared_selector_folds = assert_shape_fuzz_trace_matches_native_midfall(
        case.name,
        &params,
        pk.get_vk(),
        &generator,
        &compressed_proof,
        &repacked_proof,
        &public,
    );
    #[cfg(not(feature = "rust-verifier-trace"))]
    let compared_selector_folds = false;

    let mut wrong_public = public.to_vec();
    wrong_public[0] += F::ONE;
    assert_solidity_rejects(
        call_deployed_verifier(&mut deployed, &repacked_proof, &wrong_public),
        &format!("shape fuzz `{}` wrong public input", case.name),
    );

    let mut bad_proof = repacked_proof.clone();
    let mutation_idx = bad_proof.len() / 2;
    bad_proof[mutation_idx] ^= 0x01;
    assert_solidity_rejects(
        call_deployed_verifier(&mut deployed, &bad_proof, &public),
        &format!(
            "shape fuzz `{}` mutated proof byte {mutation_idx}",
            case.name
        ),
    );

    compared_selector_folds
}

/// Generate a random-ish supported circuit shape from a fuzz seed.
#[cfg(feature = "rust-verifier-trace")]
fn generated_shape_fuzz_spec(seed: u64) -> ShapeFuzzSpec {
    ShapeFuzzSpec {
        next_rotation: seed & 0x01 != 0,
        second_phase: seed & 0x02 != 0,
        permutation: seed & 0x04 != 0,
        lookup: seed & 0x08 != 0,
        additive_selector: seed & 0x10 != 0,
        complex_selector: seed & 0x20 != 0,
        fixed_scale: seed & 0x40 != 0,
        tag: 100 + seed.rotate_left(17) % 10_000,
    }
}

/// Circuit domain size used by the transcript differential shape fuzzer.
#[cfg(feature = "rust-verifier-trace")]
const SHAPE_FUZZ_K: u32 = 5;

/// Build test parameters covering every supplied `(shape, k)` pair.
///
/// Under `outer-single-h-commitment` the prover commits to one unsplit quotient
/// polynomial of degree `(n - 1) * quotient_poly_degree`, so a plain
/// `unsafe_setup(k)` is too small and proof generation fails with a `SrsError`
/// long after the VK builds cleanly at `k`. The monomial basis has to be larger
/// than the circuit domain while the Lagrange basis stays at `2^k` -- exactly
/// the recipe documented on `ParamsKZG::downsize_lagrange`.
///
/// Loading a real SRS is not an option for these circuits: they are generated
/// per seed, so each fixture draws its own toxic secret. Callers that share one
/// parameter set across several shapes pass them all here, and the monomial
/// basis is sized for the most demanding one.
fn shape_fuzz_params(shapes: &[(ShapeFuzzSpec, u32)], rng: &mut ChaCha8Rng) -> PoseidonParams {
    let (_, lagrange_k) = shapes.first().copied().expect("at least one shape");
    assert!(
        shapes.iter().all(|(_, k)| *k == lagrange_k),
        "one parameter set can only serve shapes that share a circuit domain size"
    );

    #[cfg(not(feature = "outer-single-h-commitment"))]
    {
        PoseidonParams::unsafe_setup(lagrange_k, rng)
    }
    #[cfg(feature = "outer-single-h-commitment")]
    {
        let extended_k = shapes
            .iter()
            .map(|(spec, k)| {
                // Configure a throwaway constraint system to learn this shape's
                // degree. keygen may compress selectors, which can only lower
                // the degree, so the uncompressed value is a safe upper bound.
                let mut cs = ConstraintSystem::<F>::default();
                <ShapeFuzzCircuit as Circuit<F>>::configure_with_params(&mut cs, *spec);
                // Same exponent `midnight_zk_stdlib::utils::plonk_api::load_srs`
                // uses for the single-h monomial basis.
                k + ((cs.degree() - 1) as f64).log2().ceil() as u32
            })
            .max()
            .expect("at least one shape");
        let mut params = PoseidonParams::unsafe_setup(extended_k, rng);
        // Keep the monomial basis extended; shrink only the Lagrange basis back
        // to the circuit domain so commitments stay at 2^k.
        params.downsize_lagrange(lagrange_k);
        params
    }
}

#[cfg(feature = "rust-verifier-trace")]
fn run_transcript_differential_shape_fuzz_case(seed: u64) {
    let spec = generated_shape_fuzz_spec(seed);
    let context = format!("transcript differential seed={seed:#018x} spec={spec:?}");
    let circuit = ShapeFuzzCircuit::new(spec, seed);
    let mut setup_rng = ChaCha8Rng::seed_from_u64(seed ^ 0x7ace_f00d);
    let params = shape_fuzz_params(&[(spec, SHAPE_FUZZ_K)], &mut setup_rng);
    let vk = keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 5)
        .unwrap_or_else(|err| panic!("{context} vk generation failed: {err:?}"));
    let pk = keygen_pk(vk, &circuit)
        .unwrap_or_else(|err| panic!("{context} pk generation failed: {err:?}"));

    let committed = [F::ZERO];
    let public = [circuit.public_instance()];
    let all_instance_columns: [&[F]; 2] = [&committed, &public];
    let mut proof_rng = ChaCha8Rng::seed_from_u64(seed ^ 0x51d1_f1ed);
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init();
    create_proof::<F, KZGCommitmentScheme<Bls12>, _, _>(
        &params,
        &pk,
        std::slice::from_ref(&circuit),
        1,
        &[&all_instance_columns],
        &mut proof_rng,
        &mut transcript,
    )
    .unwrap_or_else(|err| panic!("{context} proof generation failed: {err:?}"));
    let compressed_proof = transcript.finalize();

    let generator =
        SolidityGenerator::new(&params, pk.get_vk(), GeneratorConfig::new(public.len(), 1));
    let repacked_proof = generator
        .repack_proof(&compressed_proof)
        .unwrap_or_else(|err| panic!("{context} repack failed: {err:?}"));

    assert_shape_fuzz_trace_matches_native_midfall(
        &context,
        &params,
        pk.get_vk(),
        &generator,
        &compressed_proof,
        &repacked_proof,
        &public,
    );
}

/// Return whether expensive shape-fuzz EVM tests have their host prerequisites.
fn shape_fuzz_inputs_available_for_evm() -> bool {
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping supported-shape circuit fuzz: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return false;
    }
    // Requested but unusable is a failure, not a skip. See
    // `poseidon_inputs_available_for_evm`.
    solc_available();
    true
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_shape_fuzz_trace_matches_native_midfall(
    context: &str,
    params: &PoseidonParams,
    vk: &midnight_proofs::plonk::VerifyingKey<F, KZGCommitmentScheme<Bls12>>,
    generator: &SolidityGenerator<'_>,
    compressed_proof: &[u8],
    repacked_proof: &[u8],
    public: &[F],
) -> bool {
    use midnight_proofs::plonk::solidity_trace;

    solidity_trace::start();
    let committed_pi = [G1Projective::identity()];
    let public_columns: [&[F]; 1] = [public];
    let mut transcript = CircuitTranscript::<sha3::Keccak256>::init_from_bytes(compressed_proof);
    let guard = prepare::<F, KZGCommitmentScheme<Bls12>, CircuitTranscript<sha3::Keccak256>>(
        vk,
        &[&committed_pi],
        &[&public_columns],
        &mut transcript,
    )
    .unwrap_or_else(|err| panic!("{context} native trace prepare failed: {err:?}"));
    transcript
        .assert_empty()
        .unwrap_or_else(|_| panic!("{context} native trace transcript had trailing bytes"));
    guard
        .verify(&params.verifier_params())
        .unwrap_or_else(|err| panic!("{context} native trace guard failed: {err:?}"));
    let rust_trace = solidity_trace::take();

    let trace_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            diagnostics: RenderDiagnostics {
                trace: true,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .unwrap_or_else(|err| panic!("{context} trace render failed: {err:?}"));
    let trace_verifier_solidity = trace_artifacts.verifier;
    let trace_vk_solidity =
        trace_artifacts.verifying_key.expect("trace separate render includes VK");
    let mut deployed =
        deploy_separate_verifier_from_sources(&trace_verifier_solidity, &trace_vk_solidity);
    let (_gas, output, logs) = deployed.evm.call_with_logs(
        deployed.verifier_address,
        encode_calldata(repacked_proof, public),
    );
    let expected_true = [vec![0u8; 31], vec![1]].concat();
    assert_eq!(
        output, expected_true,
        "{context} trace verifier should accept the proof"
    );
    let mut rust_by_id = BTreeMap::new();
    for event in rust_trace {
        assert!(
            rust_by_id.insert(event.id, (event.name, event.data)).is_none(),
            "{context} duplicate Rust trace id {}",
            event.id
        );
    }
    let solidity_trace = parse_solidity_trace_logs(&logs);
    let has_selector_folds = rust_by_id
        .keys()
        .chain(solidity_trace.keys())
        .any(|id| (60_000..61_000).contains(id));
    assert_trace_equivalence_and_required_coverage(
        context,
        &rust_by_id,
        &solidity_trace,
        has_selector_folds,
    );
    has_selector_folds
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_trace_equivalence_and_required_coverage(
    context: &str,
    rust_trace: &BTreeMap<u64, (&'static str, Vec<u8>)>,
    solidity_trace: &BTreeMap<u64, Vec<u8>>,
    require_selector_folds: bool,
) {
    let missing = rust_trace
        .keys()
        .filter(|id| !solidity_trace.contains_key(id))
        .copied()
        .collect::<Vec<_>>();
    assert!(
        missing.is_empty(),
        "{context}: Solidity trace is missing native Rust trace ids {missing:?}"
    );

    let unexpected = solidity_trace
        .keys()
        .filter(|id| !rust_trace.contains_key(id))
        .copied()
        .collect::<Vec<_>>();
    assert!(
        unexpected.is_empty(),
        "{context}: Solidity trace emitted ids without a native Rust oracle {unexpected:?}"
    );

    assert_required_diff_trace_coverage_with_options(
        rust_trace,
        solidity_trace,
        require_selector_folds,
    );

    for (id, solidity_data) in solidity_trace {
        let (name, rust_data) =
            rust_trace.get(id).expect("missing Solidity trace ids were checked above");
        assert_eq!(
            rust_data,
            solidity_data,
            "{context}: trace mismatch id={id} name={name}: rust=0x{} solidity=0x{}",
            hex::encode(rust_data),
            hex::encode(solidity_data),
        );
    }
}

#[cfg(not(feature = "rust-verifier-trace"))]
#[test]
fn evm_gate_requires_native_solidity_trace_feature() {
    if env_flag_enabled(RUN_EVM_TESTS_ENV) {
        panic!(
            "{RUN_EVM_TESTS_ENV}=1 now requires the `rust-verifier-trace` feature so native/Solidity trace equivalence is part of the EVM gate"
        );
    }
}

#[test]
fn pbt_solidity_verifies_standard_plonk_embedded_vk_proofs() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_property_poseidon_positive_case(false, seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_solidity_rejects_wrong_instances() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    let strategy = (any::<u64>(), any::<bool>());
    runner
        .run(&strategy, |(seed, separate)| {
            run_property_poseidon_wrong_instance_case(separate, seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_solidity_rejects_malleated_proofs() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    let strategy = (any::<u64>(), any::<bool>(), 0usize..4096);
    runner
        .run(&strategy, |(seed, separate, bit_idx)| {
            run_property_poseidon_malleated_proof_case(separate, seed, bit_idx);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_solidity_rejects_wrong_verifying_keys() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_property_poseidon_wrong_vk_case(seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_separate_vk_digest_prefix_affects_verification() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_separate_vk_digest_prefix_affects_verification_case(seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_structured_proof_calldata_mutations_are_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_structured_proof_calldata_mutation_case(seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn pbt_proof_layout_repack_and_reader_stay_in_sync() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let mut runner = new_property_test_runner();
    runner
        .run(&any::<u64>(), |seed| {
            run_proof_layout_repack_reader_case(seed);
            Ok(())
        })
        .unwrap();
}

#[test]
fn malformed_embedded_calldata_variants_are_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let valid = encode_calldata(&fixture.proof, &fixture.instances);
    let valid_true = call_embedded_verifier_raw(&fixture.embedded_verifier_solidity, valid.clone());
    assert_solidity_accepts(valid_true, "valid embedded calldata");

    let mut wrong_selector = valid.clone();
    wrong_selector[0] ^= 0x01;

    let empty_proof = encode_calldata(&[], &fixture.instances);
    let truncated_proof = valid[..valid.len() - 1].to_vec();

    let mut extra_trailing_bytes = valid.clone();
    extra_trailing_bytes.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);

    let proof_len = fixture.proof.len();
    let instances_len_word_start = 4 + 0x40 + 0x20 + proof_len;
    let mut wrong_instance_array_length = valid.clone();
    overwrite_u256_word(
        &mut wrong_instance_array_length,
        instances_len_word_start,
        fixture.instances.len() as u64 + 1,
    );
    for (name, calldata) in [
        ("empty proof", empty_proof),
        ("truncated proof", truncated_proof),
        ("extra trailing bytes", extra_trailing_bytes),
        ("wrong selector", wrong_selector),
        ("wrong instance array length", wrong_instance_array_length),
    ] {
        let output = call_embedded_verifier_raw(&fixture.embedded_verifier_solidity, calldata);
        assert_solidity_rejects(output, name);
    }
}

#[test]
fn mutated_separate_vk_contract_is_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let mut baseline = deployed_separate_verifier(&fixture);
    assert_deployed_call_accepts(
        &mut baseline,
        &fixture,
        &fixture.proof,
        "valid proof before mutated separate vk",
    );

    let mutated_vk_solidity = mutate_first_large_hex_literal(&fixture.vk_solidity, 0);
    assert_separate_verifier_rejects_vk_mutation(
        &fixture.separate_verifier_solidity,
        &mutated_vk_solidity,
        &fixture.proof,
        &fixture.instances,
        "mutated separate vk",
    );
}

#[test]
fn vk_payload_section_mutations_are_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_poseidon_vk_sources_fixture();
    let sections = [
        ("header", "vk_digest"),
        ("quotient constants", "quotient_const"),
        ("quotient program", "quotient_program"),
        ("fixed commitments", "fixed_comms[0].x_hi"),
        ("permutation commitments", "permutation_comms[0].x_hi"),
    ];

    for (section, marker) in sections {
        assert!(
            fixture.vk_solidity.contains(marker),
            "fixture VK source missing {section} marker `{marker}`"
        );
        let mutated_vk_solidity =
            mutate_value_hex_literal_on_line_containing(&fixture.vk_solidity, marker);
        assert_separate_verifier_rejects_vk_dependency(
            &fixture.separate_verifier_solidity,
            &mutated_vk_solidity,
            &format!("mutated VK payload section: {section}"),
        );
    }
}

#[test]
fn pinned_quotient_verifier_rejects_wrong_vk_and_quotient_contracts() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let wrong_vk_solidity = mutate_first_large_hex_literal(&fixture.vk_solidity, 0);
    let wrong_quotient_solidity =
        mutate_first_large_hex_literal(&fixture.quotient_evaluator_solidity, 0);

    assert_pinned_quotient_constructor_rejects(
        &fixture.quotient_verifier_solidity,
        &wrong_vk_solidity,
        &fixture.quotient_evaluator_solidity,
        "wrong VK runtime hash",
    );
    assert_pinned_quotient_constructor_rejects(
        &fixture.quotient_verifier_solidity,
        &fixture.vk_solidity,
        &wrong_quotient_solidity,
        "wrong quotient runtime hash",
    );

    let verifier_creation_code = compile_solidity(&fixture.quotient_verifier_solidity);
    let vk_creation_code = compile_solidity(&fixture.vk_solidity);
    let quotient_creation_code = compile_solidity(&fixture.quotient_evaluator_solidity);
    assert_pinned_quotient_constructor_rejects_address_args(
        &verifier_creation_code,
        &quotient_creation_code,
        &quotient_creation_code,
        "quotient evaluator supplied as VK",
    );
    assert_pinned_quotient_constructor_rejects_address_args(
        &verifier_creation_code,
        &vk_creation_code,
        &vk_creation_code,
        "VK supplied as quotient evaluator",
    );
}

/// The verifier body is wrapped in `assembly ("memory-safe")` while writing
/// absolute addresses, which is a false promise: it never allocates through the
/// free-memory pointer. That annotation is nonetheless load-bearing -- without
/// it the block does not compile (stack too deep) -- and it is what lets solc's
/// via-IR stack-to-memory mover reserve spill slots upward from `0x80`.
///
/// The generated layout is therefore based above that reservation rather than
/// at `0x80`, so solc's spill slots and the verifier's own memory are disjoint
/// by construction instead of by a liveness coincidence. The reservation size
/// is not fixed -- observed values range from `0x80` to `0x8e0` depending on
/// the circuit, the solc release, and the optimizer schedule -- so assert the
/// property against real compiled bytecode rather than assuming it holds.
///
/// `VerifierMemoryLayout::validate()` enforces the complementary bound for the
/// generated layout: every generated region starts at or above
/// `LOW_MEMORY_SCRATCH_START`, so `reserved_end <= LOW_MEMORY_SCRATCH_START`
/// here proves full disjointness. Check both verifier and quotient evaluator
/// runtimes, because each via-IR compilation unit receives its own independent
/// spill reservation. The accumulator-bearing variants are checked too,
/// because their FinalPairing pairing-batch block adds frames and live values
/// the property fixture never renders.
#[test]
fn compiled_memoryguard_does_not_overlap_generated_layout() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    fn assert_memoryguard_clears_generated_layout(name: &str, source: &str) {
        let runtime = compile_solidity_runtime(source);
        let reserved_end = runtime_free_memory_pointer_init(&runtime).unwrap_or_else(|| {
            panic!("{name}: could not read the free-memory-pointer prologue from runtime bytecode")
        });
        assert!(
            reserved_end <= crate::lowering::layout::LOW_MEMORY_SCRATCH_START,
            "{name}: solc reserved [0x80, {reserved_end:#x}) for via-IR spill slots, which \
             overlaps the generated verifier layout based at {:#x}. A live spill slot can then \
             sit across a verifier write, silently corrupting a challenge or pairing input. \
             Raise LOW_MEMORY_SCRATCH_START above {reserved_end:#x}.",
            crate::lowering::layout::LOW_MEMORY_SCRATCH_START
        );
    }

    let fixture = create_property_poseidon_fixture();
    for (name, source) in [
        ("embedded", fixture.embedded_verifier_solidity.as_str()),
        ("separate", fixture.separate_verifier_solidity.as_str()),
        ("quotient", fixture.quotient_verifier_solidity.as_str()),
        (
            "quotient evaluator",
            fixture.quotient_evaluator_solidity.as_str(),
        ),
        (
            "trace quotient evaluator",
            fixture.trace_quotient_evaluator_solidity.as_str(),
        ),
    ] {
        assert_memoryguard_clears_generated_layout(name, source);
    }

    for (name, _, artifacts, quotient_evaluator) in render_accumulator_verifier_variants() {
        assert_memoryguard_clears_generated_layout(name, &artifacts.verifier);
        assert_memoryguard_clears_generated_layout(
            &format!("{name} quotient evaluator"),
            &quotient_evaluator,
        );
    }
}

/// `Halo2VerifyingKey` is size-checked at render time by
/// `validate_payload_layout`, because a data contract's runtime length is known
/// before compilation. The verifier's is not -- it only exists once solc has
/// run -- so nothing bounded it, and the revm harness deliberately sets
/// `limit_contract_code_size = usize::MAX` (see `evm.rs`), meaning an oversized
/// verifier would pass the whole suite and then fail to deploy on any EIP-170
/// chain. Check the compiled artifact directly.
#[test]
fn compiled_verifier_runtime_fits_the_eip170_limit() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let limit = crate::lowering::render::EIP_170_MAX_RUNTIME_BYTES;
    let fixture = create_property_poseidon_fixture();
    for (name, source) in [
        ("embedded", fixture.embedded_verifier_solidity.as_str()),
        ("separate", fixture.separate_verifier_solidity.as_str()),
        ("quotient", fixture.quotient_verifier_solidity.as_str()),
        ("vk", fixture.vk_solidity.as_str()),
    ] {
        let runtime_len = compile_solidity_runtime(source).len();
        assert!(
            runtime_len <= limit,
            "{name}: compiled runtime is {runtime_len} bytes, over the EIP-170 limit of \
             {limit}; this contract cannot be deployed on mainnet or any \
             EIP-170 chain. Note the revm harness lifts this cap, so no other test catches it."
        );
    }
}

/// Extract one rendered Yul function (signature through matching close brace)
/// from generated verifier source. The rendered helpers contain no string
/// literals, so plain brace counting is sufficient.
fn extract_yul_function<'a>(source: &'a str, signature_prefix: &str) -> &'a str {
    let start = source
        .find(signature_prefix)
        .unwrap_or_else(|| panic!("rendered source should define {signature_prefix}"));
    let tail = &source[start..];
    let open = tail.find('{').expect("function definition must open a brace");
    let mut depth = 0usize;
    for (idx, byte) in tail.bytes().enumerate().skip(open) {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return &tail[..=idx];
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced braces while extracting {signature_prefix}");
}

/// Test-only contract that runs the rendered `batch_invert` helper on
/// caller-chosen memory words. Raw calldata is `n || r || n words`; raw
/// returndata is `success flag || the n (possibly inverted) words`.
fn batch_invert_harness_source(verifier_solidity: &str) -> String {
    let batch_invert = extract_yul_function(
        verifier_solidity,
        "function batch_invert(success, mptr_start, mptr_end, scratch_mptr, r) -> ret",
    );
    let modexp_gas = crate::lowering::layout::gas::modexp_gas_word_frame();
    format!(
        r#"// SPDX-License-Identifier: CC0-1.0
pragma solidity ^0.8.24;

contract BatchInvertHarness {{
    // The extracted helper forwards the exact EIP-2565 modexp cost; mirror
    // the generated constant it references.
    uint256 internal constant MODEXP_GAS = {modexp_gas};

    fallback() external {{
        assembly {{
            {batch_invert}

            let n := calldataload(0x00)
            let r := calldataload(0x20)
            let base := 0x1000
            calldatacopy(base, 0x40, mul(n, 0x20))
            let ok := batch_invert(1, base, add(base, mul(n, 0x20)), 0x8000, r)
            mstore(0x80, ok)
            mcopy(0xa0, base, mul(n, 0x20))
            return(0x80, add(0x20, mul(n, 0x20)))
        }}
    }}
}}
"#
    )
}

/// Execute the rendered `batch_invert` helper against adversarial words.
///
/// The template greps in `lowering/tests.rs` pin the guard text; this pins
/// the behavior: the singleton and general paths must both fail closed on
/// words outside the canonical range (`x >= r`, including invertible
/// residues, `x = r`, and literal zero) without touching the input run,
/// so accept/reject semantics never depend on batch length. Canonical
/// batches must produce exactly the native inverses.
#[test]
fn batch_invert_fails_closed_on_noncanonical_words_in_all_paths() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let harness = batch_invert_harness_source(&fixture.embedded_verifier_solidity);
    let mut evm = Evm::default();
    let address = evm.create(compile_solidity(&harness));

    let r = fr_modulus_u256();
    let mut run = |elems: &[U256]| -> (bool, Vec<U256>) {
        let mut calldata = Vec::with_capacity((2 + elems.len()) * 0x20);
        calldata.extend_from_slice(&U256::from(elems.len()).to_be_bytes::<0x20>());
        calldata.extend_from_slice(&r.to_be_bytes::<0x20>());
        for elem in elems {
            calldata.extend_from_slice(&elem.to_be_bytes::<0x20>());
        }
        match evm.try_call(address, calldata) {
            CallOutcome::Success { output, .. } => {
                assert_eq!(
                    output.len(),
                    (1 + elems.len()) * 0x20,
                    "harness returndata shape"
                );
                let flag = U256::try_from_be_slice(&output[..0x20]).unwrap();
                assert!(flag <= U256::from(1), "success flag must be boolean");
                let words = output[0x20..]
                    .chunks_exact(0x20)
                    .map(|word| U256::try_from_be_slice(word).unwrap())
                    .collect();
                (flag == U256::from(1), words)
            }
            outcome => panic!("harness must not revert or halt: {outcome:?}"),
        }
    };

    let word = |value: u64| U256::from(value);
    let inv =
        |value: u64| crate::lowering::encoding::fe_to_u256::<F>(F::from(value).invert().unwrap());

    // Canonical batches succeed and invert every element in place; the
    // lengths cover the empty, singleton, two-element, and looped general
    // paths.
    let (ok, out) = run(&[]);
    assert!(ok, "empty batch must be a no-op success");
    assert!(out.is_empty());
    for elems in [vec![7u64], vec![2, 3], vec![1, 2, 3, 5, 7]] {
        let input: Vec<U256> = elems.iter().copied().map(word).collect();
        let (ok, out) = run(&input);
        assert!(ok, "canonical batch of {} must succeed", elems.len());
        let expected: Vec<U256> = elems.iter().copied().map(inv).collect();
        assert_eq!(
            out,
            expected,
            "batch of {} must produce native inverses",
            elems.len()
        );
    }

    // Every rejection leaves the input run untouched: zero and anything
    // congruent to zero mod r has no inverse, and non-canonical words with
    // invertible residues (x = r + 5, 2^256 - 1) must fail closed in both
    // paths rather than being reduced by mulmod. The three r + 5 positions
    // hit the general path's first-element, loop, and final-element guards.
    let r_plus_5 = r + word(5);
    for (name, elems) in [
        ("singleton literal zero", vec![U256::ZERO]),
        ("singleton x = r", vec![r]),
        ("singleton x = r + 5", vec![r_plus_5]),
        ("singleton x = 2^256 - 1", vec![U256::MAX]),
        ("general literal zero", vec![word(2), U256::ZERO, word(3)]),
        ("general x = r", vec![word(2), r, word(3)]),
        (
            "general first element x = r + 5",
            vec![r_plus_5, word(2), word(3)],
        ),
        (
            "general loop element x = r + 5",
            vec![word(2), r_plus_5, word(3)],
        ),
        (
            "general final element x = r + 5",
            vec![word(2), word(3), r_plus_5],
        ),
        (
            "general two-element x = 2^256 - 1",
            vec![word(2), U256::MAX],
        ),
    ] {
        let (ok, out) = run(&elems);
        assert!(!ok, "{name} must fail closed");
        assert_eq!(out, elems, "{name} must leave the input words untouched");
    }
}

#[test]
fn verifier_constructor_rejects_missing_or_mismatched_eip2537_precompiles() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    for (name, needle, replacement) in [
        (
            "missing G1ADD precompile",
            "staticcall(G1ADD_GAS, 0x0b",
            "staticcall(G1ADD_GAS, 0x12",
        ),
        (
            "G1MSM routed to G1ADD",
            "staticcall(G1MSM_GAS_1PAIR, 0x0c",
            "staticcall(G1MSM_GAS_1PAIR, 0x0b",
        ),
        (
            "pairing routed to G1MSM",
            "staticcall(PAIRING_GAS_2PAIR, 0x0f",
            "staticcall(PAIRING_GAS_2PAIR, 0x0c",
        ),
    ] {
        let verifier_solidity = replace_required_precompile_staticcall(
            &fixture.quotient_verifier_solidity,
            needle,
            replacement,
        );
        assert_pinned_quotient_constructor_rejects(
            &verifier_solidity,
            &fixture.vk_solidity,
            &fixture.quotient_evaluator_solidity,
            name,
        );
    }
}

#[test]
fn production_renders_do_not_emit_gas_checkpoints() {
    // The fixture's base variants follow `RenderDiagnostics::default()`, so a
    // `solidity-trace` build makes them emit LOG1 and drop `view` for the same
    // reason a gas-checkpoint build does. Both are intended diagnostic shapes,
    // not production renders, so neither can satisfy the assertions below.
    if crate::SOLIDITY_GAS_CHECKPOINTS_ENABLED || crate::SOLIDITY_TRACE_ENABLED {
        return;
    }
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    for (name, source) in [
        ("embedded", fixture.embedded_verifier_solidity.as_str()),
        ("separate", fixture.separate_verifier_solidity.as_str()),
        (
            "quotient-separated",
            fixture.quotient_verifier_solidity.as_str(),
        ),
    ] {
        assert!(
            !source.contains("function gas_checkpoint"),
            "{name} production render unexpectedly defines gas_checkpoint"
        );
        assert!(
            !source.contains("log1("),
            "{name} production render unexpectedly emits LOG1"
        );
        assert!(
            source.contains(") external view returns (bool)"),
            "{name} production render should keep verifyProof external view"
        );
    }
}

#[test]
fn production_separate_verifier_accepts_valid_proof_under_staticcall() {
    // The fixture renders its base variants with `RenderDiagnostics::default()`,
    // which follows the crate's feature flags. A trace or gas-checkpoint build
    // emits LOG1 and is deliberately not `view`, so it cannot be STATICCALL-ed
    // -- that is the documented contract, not a regression. Skip on those
    // builds, matching `production_renders_do_not_emit_gas_checkpoints`.
    if crate::SOLIDITY_TRACE_ENABLED || crate::SOLIDITY_GAS_CHECKPOINTS_ENABLED {
        return;
    }
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let mut deployed = deployed_separate_verifier(&fixture);
    assert_deployed_call_accepts(&mut deployed, &fixture, &fixture.proof, "valid proof");

    let harness_address = deployed.evm.create_with_address_arg(
        compile_solidity(STATICCALL_VERIFIER_HARNESS),
        deployed.verifier_address,
    );
    deployed.verifier_address = harness_address;

    let verifier_calldata = encode_calldata(&fixture.proof, &fixture.instances);
    let harness_calldata = encode_bytes_call("check(bytes)", &verifier_calldata);
    assert_solidity_accepts(
        call_deployed_verifier_raw(&mut deployed, harness_calldata),
        "valid proof through STATICCALL harness",
    );
}

#[test]
fn standard_plonk_render_is_deterministic_for_same_seed() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture_a = load_property_poseidon_fixture();
    let fixture_b = load_property_poseidon_fixture();

    assert_eq!(fixture_a.instances, fixture_b.instances);
    assert_eq!(fixture_a.proof.len(), fixture_b.proof.len());
    assert_eq!(
        fixture_a.embedded_verifier_solidity,
        fixture_b.embedded_verifier_solidity
    );
    assert_eq!(
        fixture_a.separate_verifier_solidity,
        fixture_b.separate_verifier_solidity
    );
    assert_eq!(fixture_a.vk_solidity, fixture_b.vk_solidity);
}

#[test]
fn compile_solidity_is_deterministic_for_same_source() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let bytecode_a = compile_solidity(&fixture.embedded_verifier_solidity);
    let bytecode_b = compile_solidity(&fixture.embedded_verifier_solidity);

    assert_eq!(bytecode_a, bytecode_b);
}

/// The accumulator fixed-base scalar tail must match the verifying key.
///
/// `fixed_scalar_count` is derived from `num_instances`, but the bases those
/// scalars multiply are generated as `fixed_comm_mptr + i * 0x80` from the VK.
/// A tail longer than the VK's fixed-commitment count used to render fine and
/// silently emit base pointers past that region, aliasing permutation
/// commitments -- and beyond them arbitrary VK payload words -- as accumulator
/// G1 bases.
#[test]
fn accumulator_fixed_base_tail_must_match_verifying_key() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let srs_dir = srs_dir();
    env::set_var("SRS_DIR", &srs_dir);
    let relation = PoseidonExample;
    let srs = poseidon_srs_for_test(&relation);
    let vk = setup_vk(&srs, &relation);

    let num_fixed_comms = vk.vk().fixed_commitments().len();
    let num_permutation_comms = vk.vk().permutation().commitments().len();
    let collapsed = AccumulatorEncoding::FULLY_COLLAPSED_PUBLIC_INPUT_WORDS;
    // `-G` plus every permutation commitment, then up to one scalar per fixed
    // commitment.
    let min_tail = 1 + num_permutation_comms;
    let max_tail = min_tail + num_fixed_comms;

    // A tail three scalars longer than the VK can supply bases for. Before the
    // guard this rendered a verifier whose last three "fixed bases" were
    // permutation commitments.
    let err = SolidityGenerator::try_new(
        &srs,
        vk.vk(),
        GeneratorConfig::new(collapsed + max_tail + 3, 1)
            .with_accumulator(AccumulatorEncoding::new(0, 7, 56)),
    )
    .expect_err("oversized accumulator fixed-base tail should be rejected");
    assert!(
        matches!(
            err,
            crate::GeneratorError::AccumulatorFixedBaseTailMismatch {
                fixed_scalar_count,
                max_fixed_scalar_count,
                ..
            } if fixed_scalar_count == max_tail + 3 && max_fixed_scalar_count == max_tail
        ),
        "unexpected error for oversized tail: {err}"
    );

    // A tail too short to cover `-G` plus the permutation commitments would
    // underflow the base count in the artifact emitter.
    SolidityGenerator::try_new(
        &srs,
        vk.vk(),
        GeneratorConfig::new(collapsed + min_tail - 1, 1)
            .with_accumulator(AccumulatorEncoding::new(0, 7, 56)),
    )
    .expect_err("undersized accumulator fixed-base tail should be rejected");

    // Supported shapes still build: no tail at all, the full base set, and a
    // prefix of the fixed commitments in between (every pointer stays inside
    // the fixed-commitment region).
    for num_instances in [
        collapsed,
        collapsed + min_tail,
        collapsed + max_tail,
        collapsed + (min_tail + max_tail) / 2,
    ] {
        SolidityGenerator::try_new(
            &srs,
            vk.vk(),
            GeneratorConfig::new(num_instances, 1)
                .with_accumulator(AccumulatorEncoding::new(0, 7, 56)),
        )
        .unwrap_or_else(|err| panic!("supported accumulator tail should build: {err}"));
    }
}

/// Render the three accumulator-bearing verifier variants over the Poseidon
/// fixture VK: fully collapsed, fixed-base scalar tail, and point-pair
/// encodings. Returns `(name, has_carried_scalars, artifacts, evaluator)` per
/// variant.
fn render_accumulator_verifier_variants(
) -> Vec<(&'static str, bool, crate::RenderedArtifacts, String)> {
    let srs_dir = srs_dir();
    env::set_var("SRS_DIR", &srs_dir);
    let relation = PoseidonExample;
    let srs = poseidon_srs_for_test(&relation);
    let vk = setup_vk(&srs, &relation);

    // A fully collapsed accumulator occupies FULLY_COLLAPSED_PUBLIC_INPUT_WORDS
    // public inputs and has no fixed-base scalar tail.
    let collapsed_words = AccumulatorEncoding::FULLY_COLLAPSED_PUBLIC_INPUT_WORDS;
    // The partially collapsed form appends one scalar per generated base:
    // `-G`, then every fixed commitment, then every permutation commitment.
    let num_fixed_comms = vk.vk().fixed_commitments().len();
    let num_perm_comms = vk.vk().permutation().commitments().len();
    let tail_words = 1 + num_fixed_comms + num_perm_comms;

    let variants = [
        (
            "fully collapsed accumulator",
            collapsed_words,
            AccumulatorEncoding::new(0, 7, 56),
            true,
        ),
        (
            "accumulator with fixed-base scalar tail",
            collapsed_words + tail_words,
            AccumulatorEncoding::new(0, 7, 56),
            true,
        ),
        // Point-pair encodings carry no explicit scalars -- both are implicit
        // one -- so no calldata scalar is read and none is range-checked.
        (
            "point-pair accumulator",
            AccumulatorEncoding::POINT_PAIR_PUBLIC_INPUT_WORDS,
            AccumulatorEncoding::point_pair(0, 7, 56),
            false,
        ),
    ];

    variants
        .into_iter()
        .map(|(name, num_instances, acc, has_carried_scalars)| {
            let generator = SolidityGenerator::new(
                &srs,
                vk.vk(),
                GeneratorConfig::new(num_instances, 1).with_accumulator(acc),
            );
            let artifacts = generator
                .render(RenderOptions {
                    vk: RenderVk::Separate,
                    ..RenderOptions::default()
                })
                .unwrap_or_else(|err| panic!("{name} should render: {err}"));
            let quotient_evaluator = generator
                .render_quotient_evaluator(RenderDiagnostics::default())
                .unwrap_or_else(|err| panic!("{name} quotient evaluator should render: {err}"));
            (name, has_carried_scalars, artifacts, quotient_evaluator)
        })
        .collect()
}

/// Compile the accumulator render arm.
///
/// No production fixture enables `with_accumulator`, so before this test the
/// whole `{%- if self.expected_has_accumulator %}` branch of
/// AccumulatorHelpers.yul -- the limb decoder, the pre-transcript
/// public-accumulator MSM, and the fixed-base scalar tail -- was never handed
/// to solc by the default gate. Only the opt-in `ivc_keccak_solidity` bench
/// (k = 20, release, external SRS assets) rendered it, so a Yul syntax error
/// or a solc stack-depth regression in that branch could reach a release
/// unnoticed.
///
/// This does not execute the accumulator logic against a real recursive proof
/// -- that still needs a decider circuit carrying a genuine accumulator in its
/// public inputs. It does guarantee the branch compiles, and it pins the
/// canonicality checks on the scalars the helper feeds to G1MSM.
#[test]
fn accumulator_verifier_variants_compile_with_pinned_solc() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    for (name, has_carried_scalars, artifacts, _) in render_accumulator_verifier_variants() {
        let verifier = artifacts.verifier;
        assert!(
            verifier.contains("function validate_public_accumulator"),
            "{name} should render the accumulator helper"
        );
        // The helper runs before the transcript loop that rejects
        // non-canonical instance words, and EIP-2537 G1MSM reduces scalars mod
        // r implicitly, so it must reject `s >= r` itself.
        if has_carried_scalars {
            for required in ["lt(lhs_scalar, r)", "lt(rhs_scalar, r)"] {
                assert!(
                    verifier.contains(required),
                    "{name} should range-check accumulator scalars: {required}"
                );
            }
        } else {
            assert!(
                !verifier.contains("lt(lhs_scalar, r)"),
                "{name} carries no explicit scalars, so none should be read or checked"
            );
        }

        for (label, source) in [
            (name, verifier.as_str()),
            (
                "accumulator VK",
                artifacts.verifying_key.as_deref().expect("separate render includes VK"),
            ),
        ] {
            let bytecode = std::panic::catch_unwind(AssertUnwindSafe(|| compile_solidity(source)))
                .unwrap_or_else(|_| panic!("{label} should compile under the pinned solc"));
            assert!(
                !bytecode.is_empty(),
                "{label} should compile to non-empty bytecode"
            );
        }
    }
}

#[test]
fn poseidon_verifier_variants_compile_with_pinned_solc() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let variants = [
        (
            "embedded verifier",
            fixture.embedded_verifier_solidity.as_str(),
        ),
        (
            "embedded trace verifier",
            fixture.embedded_trace_verifier_solidity.as_str(),
        ),
        (
            "embedded gas verifier",
            fixture.embedded_gas_verifier_solidity.as_str(),
        ),
        (
            "separate verifier",
            fixture.separate_verifier_solidity.as_str(),
        ),
        (
            "separate gas verifier",
            fixture.gas_separate_verifier_solidity.as_str(),
        ),
        (
            "separate trace verifier",
            fixture.trace_verifier_solidity.as_str(),
        ),
        ("separate VK", fixture.vk_solidity.as_str()),
        ("separate trace VK", fixture.trace_vk_solidity.as_str()),
        (
            "external quotient verifier",
            fixture.quotient_verifier_solidity.as_str(),
        ),
        (
            "external quotient evaluator",
            fixture.quotient_evaluator_solidity.as_str(),
        ),
        (
            "external quotient trace verifier",
            fixture.trace_quotient_verifier_solidity.as_str(),
        ),
        (
            "external quotient trace evaluator",
            fixture.trace_quotient_evaluator_solidity.as_str(),
        ),
        (
            "external quotient trace VK",
            fixture.trace_quotient_vk_solidity.as_str(),
        ),
    ];

    for (name, source) in variants {
        let bytecode = std::panic::catch_unwind(AssertUnwindSafe(|| compile_solidity(source)))
            .unwrap_or_else(|_| panic!("{name} did not compile"));
        assert!(!bytecode.is_empty(), "{name} compiled to empty bytecode");
    }
}

#[cfg(feature = "rust-verifier-trace")]
#[test]
fn native_midfall_verifier_trace_matches_solidity_trace() {
    use group::Group;
    use midnight_curves::{Bls12, G1Projective};
    use midnight_proofs::{
        plonk::{prepare, solidity_trace},
        poly::{commitment::Guard, kzg::KZGCommitmentScheme},
        transcript::{CircuitTranscript, Transcript},
    };

    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();

    solidity_trace::start();
    let mut transcript =
        CircuitTranscript::<sha3::Keccak256>::init_from_bytes(&fixture.compressed_proof);
    let committed_pi = vec![G1Projective::identity()];
    let public_columns: [&[F]; 1] = [&fixture.instances];
    let guard = prepare::<F, KZGCommitmentScheme<Bls12>, CircuitTranscript<sha3::Keccak256>>(
        fixture.vk.vk(),
        &[&committed_pi],
        &[&public_columns],
        &mut transcript,
    )
    .expect("native prepare succeeds");
    transcript.assert_empty().expect("native transcript consumes proof");
    guard.verify(&fixture.params_verifier).expect("native guard verifies");
    let rust_trace = solidity_trace::take();

    let mut evm = Evm::default();
    let vk_address = evm.create(compile_solidity(&fixture.trace_vk_solidity));
    let verifier_address = evm.create_with_address_arg(
        compile_solidity(&fixture.trace_verifier_solidity),
        vk_address,
    );
    let (_gas, output, logs) = evm.call_with_logs(
        verifier_address,
        encode_calldata(&fixture.proof, &fixture.instances),
    );
    let solidity_returned_success = output == [vec![0; 31], vec![1]].concat();
    let solidity_trace = parse_solidity_trace_logs(&logs);

    let mut rust_by_id = BTreeMap::new();
    for event in rust_trace {
        assert!(
            rust_by_id.insert(event.id, (event.name, event.data)).is_none(),
            "duplicate Rust trace id {}",
            event.id
        );
    }
    assert_required_diff_trace_coverage(&rust_by_id, &solidity_trace);

    assert_eq!(
        rust_by_id.keys().copied().collect::<Vec<_>>(),
        solidity_trace.keys().copied().collect::<Vec<_>>(),
        "Rust/Solidity trace ID sets differ"
    );

    for (id, solidity_data) in solidity_trace {
        let (name, rust_data) = rust_by_id.get(&id).expect("Rust trace id present");
        assert_eq!(
            rust_data,
            &solidity_data,
            "trace mismatch id={id} name={name}: rust=0x{} solidity=0x{}",
            hex::encode(rust_data),
            hex::encode(&solidity_data),
        );
    }

    assert!(
        solidity_returned_success,
        "trace verifier returned failure after matching Rust trace"
    );
}

#[test]
fn trace_verifiers_revert_on_final_pairing_failure() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let mut bad_instances = fixture.instances.clone();
    bad_instances[0] += F::ONE;

    assert_solidity_rejects(
        call_embedded_verifier(
            &fixture.embedded_trace_verifier_solidity,
            &fixture.proof,
            &bad_instances,
        ),
        "embedded trace verifier wrong instance",
    );
    assert_solidity_rejects(
        call_separate_verifier(
            &fixture.trace_verifier_solidity,
            &fixture.trace_vk_solidity,
            &fixture.proof,
            &bad_instances,
        ),
        "separate trace verifier wrong instance",
    );
}

#[cfg(feature = "rust-verifier-trace")]
fn parse_solidity_trace_logs(logs: &[revm::primitives::Log]) -> BTreeMap<u64, Vec<u8>> {
    let mut trace = BTreeMap::new();

    for log in logs {
        let topics = log.data.topics();
        assert_eq!(topics.len(), 1, "trace log must have one topic");

        let data = log.data.data.as_ref().to_vec();
        if data.is_empty() {
            continue;
        }

        let id = trace_topic_id(topics[0]);
        assert!(
            trace.insert(id, data).is_none(),
            "duplicate Solidity trace id {id}"
        );
    }

    trace
}

#[cfg(feature = "rust-verifier-trace")]
fn trace_topic_id(topic: B256) -> u64 {
    let bytes = topic.as_slice();
    u64::from_be_bytes(bytes[24..32].try_into().expect("topic is 32 bytes"))
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_required_diff_trace_coverage(
    rust_trace: &BTreeMap<u64, (&'static str, Vec<u8>)>,
    solidity_trace: &BTreeMap<u64, Vec<u8>>,
) {
    assert_required_diff_trace_coverage_with_options(rust_trace, solidity_trace, true);
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_required_diff_trace_coverage_with_options(
    rust_trace: &BTreeMap<u64, (&'static str, Vec<u8>)>,
    solidity_trace: &BTreeMap<u64, Vec<u8>>,
    require_selector_folds: bool,
) {
    for (name, id) in [
        ("theta challenge", 7),
        ("beta challenge", 8),
        ("gamma challenge", 9),
        ("y challenge", 10),
        ("x challenge", 11),
        ("x1 challenge", 13),
        ("x2 challenge", 14),
        ("x3 challenge", 15),
        ("x4 challenge", 16),
        ("quotient numerator", 36),
        ("f_eval", 31),
        ("final MSM commitment", 33),
        ("pairing lhs input", 27),
        ("pairing rhs input", 28),
        ("final pairing result", 35),
    ] {
        assert_trace_id_present(rust_trace, solidity_trace, id, name);
    }

    assert_trace_range_present(
        rust_trace,
        solidity_trace,
        30_000..40_000,
        "quotient identity evaluations",
    );
    assert_trace_range_present(
        rust_trace,
        solidity_trace,
        40_000..41_000,
        "PCS q_com point-set commitments",
    );
    assert_trace_range_present(
        rust_trace,
        solidity_trace,
        41_000..42_000,
        "serialized PCS point sets",
    );
    if require_selector_folds {
        assert_trace_range_present(rust_trace, solidity_trace, 60_000..61_000, "selector folds");
    }
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_trace_id_present(
    rust_trace: &BTreeMap<u64, (&'static str, Vec<u8>)>,
    solidity_trace: &BTreeMap<u64, Vec<u8>>,
    id: u64,
    name: &str,
) {
    assert!(
        rust_trace.contains_key(&id),
        "Rust trace missing required {name} id {id}"
    );
    assert!(
        solidity_trace.contains_key(&id),
        "Solidity trace missing required {name} id {id}"
    );
}

#[cfg(feature = "rust-verifier-trace")]
fn assert_trace_range_present(
    rust_trace: &BTreeMap<u64, (&'static str, Vec<u8>)>,
    solidity_trace: &BTreeMap<u64, Vec<u8>>,
    range: std::ops::Range<u64>,
    name: &str,
) {
    assert!(
        rust_trace.keys().any(|id| range.contains(id)),
        "Rust trace missing required {name} in id range {range:?}"
    );
    assert!(
        solidity_trace.keys().any(|id| range.contains(id)),
        "Solidity trace missing required {name} in id range {range:?}"
    );
}

#[derive(Clone, Debug)]
struct PoseidonExample;

impl Relation for PoseidonExample {
    /// Public output field element for the Poseidon relation.
    type Instance = F;

    /// Three-field-element Poseidon preimage.
    type Witness = [F; 3];

    /// Format the Poseidon output as one public instance.
    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    /// Build the Poseidon circuit using the zk-stdlib helper chips.
    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let assigned_message = std_lib.assign_many(layouter, &witness.transpose_array())?;
        let output = std_lib.poseidon(layouter, &assigned_message)?;
        std_lib.constrain_as_public_input(layouter, &output)
    }

    /// Declare the Poseidon chip dependency for setup helpers.
    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            ..ZkStdLibArch::default()
        }
    }

    /// Relation serialization is unused for this in-memory fixture.
    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    /// Relation deserialization returns the stateless fixture.
    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(PoseidonExample)
    }
}

#[derive(Clone, Debug)]
struct PropertyPoseidonFixture {
    compressed_proof: Vec<u8>,
    proof: Vec<u8>,
    proof_layout: crate::lowering::abi::ProofCalldataLayout,
    scalar_layout: crate::lowering::RepackedProofScalarLayout,
    instances: Vec<F>,
    params_verifier: PoseidonVerifierParams,
    vk: MidnightVK,
    embedded_verifier_solidity: String,
    embedded_trace_verifier_solidity: String,
    embedded_gas_verifier_solidity: String,
    separate_verifier_solidity: String,
    gas_separate_verifier_solidity: String,
    vk_solidity: String,
    quotient_verifier_solidity: String,
    quotient_evaluator_solidity: String,
    trace_quotient_evaluator_solidity: String,
    trace_quotient_verifier_solidity: String,
    trace_quotient_vk_solidity: String,
    #[allow(dead_code)]
    trace_verifier_solidity: String,
    #[allow(dead_code)]
    trace_vk_solidity: String,
}

#[derive(Clone)]
struct PoseidonVkSourcesFixture {
    separate_verifier_solidity: String,
    vk_solidity: String,
}

/// Cached separate-VK Solidity sources for constructor/pinning tests.
fn create_poseidon_vk_sources_fixture() -> PoseidonVkSourcesFixture {
    static FIXTURE: OnceLock<PoseidonVkSourcesFixture> = OnceLock::new();
    FIXTURE.get_or_init(load_poseidon_vk_sources_fixture).clone()
}

/// Build the separate verifier and VK source fixture.
fn load_poseidon_vk_sources_fixture() -> PoseidonVkSourcesFixture {
    let srs_dir = srs_dir();
    env::set_var("SRS_DIR", &srs_dir);

    let relation = PoseidonExample;
    let srs = poseidon_srs_for_test(&relation);
    let vk = setup_vk(&srs, &relation);
    assert_eq!(vk.k() as u32, POSEIDON_K, "unexpected Poseidon VK k");

    let generator = SolidityGenerator::new(&srs, vk.vk(), GeneratorConfig::new(1, 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("separate render");
    let separate_verifier_solidity = artifacts.verifier;
    let vk_solidity = artifacts.verifying_key.expect("separate render includes VK");

    PoseidonVkSourcesFixture {
        separate_verifier_solidity,
        vk_solidity,
    }
}

/// Cached full Poseidon fixture used by property-style tests.
fn create_property_poseidon_fixture() -> PropertyPoseidonFixture {
    static FIXTURE: OnceLock<PropertyPoseidonFixture> = OnceLock::new();
    FIXTURE.get_or_init(load_property_poseidon_fixture).clone()
}

/// Generate proofs, render verifier variants, and cache host-side layouts.
fn load_property_poseidon_fixture() -> PropertyPoseidonFixture {
    let srs_dir = srs_dir();
    env::set_var("SRS_DIR", &srs_dir);

    let relation = PoseidonExample;
    let srs = poseidon_srs_for_test(&relation);
    let vk = setup_vk(&srs, &relation);
    assert_eq!(vk.k() as u32, POSEIDON_K, "unexpected Poseidon VK k");

    let (compressed_proof, instance) = generate_poseidon_proof(&srs, &relation, &vk);

    let generator = SolidityGenerator::new(&srs, vk.vk(), GeneratorConfig::new(1, 1));
    let embedded_verifier_solidity =
        generator.render(RenderOptions::default()).expect("embedded render").verifier;
    let embedded_trace_verifier_solidity = generator
        .render(RenderOptions {
            diagnostics: RenderDiagnostics {
                trace: true,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .expect("embedded trace render")
        .verifier;
    let embedded_gas_verifier_solidity = generator
        .render(RenderOptions {
            diagnostics: RenderDiagnostics {
                gas_checkpoints: true,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .expect("embedded gas render")
        .verifier;
    let separate_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("separate render");
    let separate_verifier_solidity = separate_artifacts.verifier;
    let vk_solidity = separate_artifacts.verifying_key.expect("separate render includes VK");
    let gas_separate_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            diagnostics: RenderDiagnostics {
                gas_checkpoints: true,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .expect("separate gas render");
    let gas_separate_verifier_solidity = gas_separate_artifacts.verifier;
    let gas_vk_solidity =
        gas_separate_artifacts.verifying_key.expect("separate gas render includes VK");
    assert_eq!(
        vk_solidity, gas_vk_solidity,
        "plain and gas-checkpoint render paths must share the same VK"
    );
    let quotient_evaluator_solidity = generator
        .render_quotient_evaluator(RenderDiagnostics::default())
        .expect("quotient evaluator render");
    let quotient_creation_code = compile_solidity(&quotient_evaluator_solidity);
    let mut pin_evm = Evm::default();
    let quotient_address = pin_evm.create(quotient_creation_code);
    let quotient_runtime_size = pin_evm.code_size(quotient_address);
    let quotient_codehash = pin_evm.code_hash(quotient_address);
    let trace_quotient_evaluator_solidity = generator
        .render_quotient_evaluator(RenderDiagnostics {
            trace: true,
            ..RenderDiagnostics::default()
        })
        .expect("trace quotient evaluator render");
    let trace_quotient_creation_code = compile_solidity(&trace_quotient_evaluator_solidity);
    let mut trace_pin_evm = Evm::default();
    let trace_quotient_address = trace_pin_evm.create(trace_quotient_creation_code);
    let trace_quotient_runtime_size = trace_pin_evm.code_size(trace_quotient_address);
    let trace_quotient_codehash = trace_pin_evm.code_hash(trace_quotient_address);
    let quotient_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            quotient: RenderQuotient::ExternalPinned {
                runtime_len: quotient_runtime_size,
                codehash: quotient_codehash,
            },
            ..RenderOptions::default()
        })
        .expect("separate pinned render with quotient evaluator");
    let quotient_verifier_solidity = quotient_artifacts.verifier;
    let quotient_vk_solidity =
        quotient_artifacts.verifying_key.expect("pinned separate render includes VK");
    let pinned_quotient_solidity = quotient_artifacts
        .quotient_evaluator
        .expect("pinned render includes quotient evaluator");
    let trace_quotient_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            quotient: RenderQuotient::ExternalPinned {
                runtime_len: trace_quotient_runtime_size,
                codehash: trace_quotient_codehash,
            },
            diagnostics: RenderDiagnostics {
                trace: true,
                ..RenderDiagnostics::default()
            },
            provenance: None,
        })
        .expect("trace pinned render with quotient evaluator");
    let trace_quotient_verifier_solidity = trace_quotient_artifacts.verifier;
    let trace_quotient_vk_solidity = trace_quotient_artifacts
        .verifying_key
        .expect("trace pinned separate render includes VK");
    let trace_pinned_quotient = trace_quotient_artifacts
        .quotient_evaluator
        .expect("trace pinned render includes quotient evaluator");
    assert_eq!(
        quotient_evaluator_solidity, pinned_quotient_solidity,
        "pinning the quotient evaluator must not change the evaluator source"
    );
    assert_eq!(
        trace_quotient_evaluator_solidity, trace_pinned_quotient,
        "trace pinning must not change the trace quotient evaluator source"
    );
    assert_eq!(
        vk_solidity, quotient_vk_solidity,
        "plain and quotient-separated render paths must share the same VK"
    );
    assert_eq!(
        vk_solidity, trace_quotient_vk_solidity,
        "plain and trace quotient-separated render paths must share the same VK"
    );
    let trace_artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            diagnostics: RenderDiagnostics {
                trace: true,
                ..RenderDiagnostics::default()
            },
            ..RenderOptions::default()
        })
        .expect("trace render");
    let trace_verifier_solidity = trace_artifacts.verifier;
    let trace_vk_solidity =
        trace_artifacts.verifying_key.expect("trace separate render includes VK");
    let proof_layout = generator.inputs().lowering_plan().proof_layout;
    let proof = generator.repack_proof(&compressed_proof).expect("proof repack");
    let scalar_layout = generator.repacked_proof_scalar_layout_for_test();
    let params_verifier = srs.verifier_params();

    PropertyPoseidonFixture {
        compressed_proof,
        proof,
        proof_layout,
        scalar_layout,
        instances: vec![instance],
        params_verifier,
        vk,
        embedded_verifier_solidity,
        embedded_trace_verifier_solidity,
        embedded_gas_verifier_solidity,
        separate_verifier_solidity,
        gas_separate_verifier_solidity,
        vk_solidity,
        quotient_verifier_solidity,
        quotient_evaluator_solidity,
        trace_quotient_evaluator_solidity,
        trace_quotient_verifier_solidity,
        trace_quotient_vk_solidity,
        trace_verifier_solidity,
        trace_vk_solidity,
    }
}

#[test]
fn every_proof_scalar_rejects_fr_modulus() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let r_be = fr_modulus_be_word();
    let scalar_offsets = proof_scalar_offsets(&fixture);
    assert!(
        !scalar_offsets.is_empty(),
        "fixture proof should expose scalar fields to range-check"
    );

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (name, offset) in scalar_offsets {
        let mut bad_proof = fixture.proof.clone();
        bad_proof[offset..offset + 0x20].copy_from_slice(&r_be);
        assert_deployed_call_rejects(
            &mut evm,
            &fixture,
            &bad_proof,
            &format!("{name} scalar equal to Fr modulus at proof offset {offset}"),
        );
    }
}

#[test]
fn every_proof_scalar_rejects_boundary_values() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let scalar_offsets = proof_scalar_offsets(&fixture);
    assert!(
        !scalar_offsets.is_empty(),
        "fixture proof should expose scalar fields to mutate"
    );

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    let r = fr_modulus_u256();
    let static_variants = [
        ("zero", U256::from(0u64).to_be_bytes::<32>()),
        ("one", U256::from(1u64).to_be_bytes::<32>()),
        ("Fr_minus_one", (r - U256::from(1u64)).to_be_bytes::<32>()),
    ];

    for (name, offset) in scalar_offsets {
        let original_word: [u8; 32] =
            fixture.proof[offset..offset + 0x20].try_into().expect("proof scalar word");
        let original = U256::from_be_bytes(original_word);
        let original_plus_r = original + r;

        for (variant, word) in static_variants
            .into_iter()
            .chain([("original_plus_Fr", original_plus_r.to_be_bytes::<32>())])
        {
            if word == original_word {
                continue;
            }
            let mut bad_proof = fixture.proof.clone();
            bad_proof[offset..offset + 0x20].copy_from_slice(&word);
            assert_deployed_call_rejects(
                &mut evm,
                &fixture,
                &bad_proof,
                &format!("{name} scalar replaced with {variant} at proof offset {offset}"),
            );
        }
    }
}

#[test]
fn every_proof_scalar_rejects_high_bit_noncanonical_values() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let scalar_offsets = proof_scalar_offsets(&fixture);
    assert!(
        !scalar_offsets.is_empty(),
        "fixture proof should expose scalar fields to mutate"
    );

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (scalar_idx, (name, offset)) in scalar_offsets.into_iter().enumerate() {
        let mut high_bit = [0u8; 32];
        high_bit[0] = 0x80;

        let mut deterministic_noncanonical = [0u8; 32];
        for (byte_idx, byte) in deterministic_noncanonical.iter_mut().enumerate() {
            *byte = (scalar_idx as u8)
                .wrapping_mul(31)
                .wrapping_add((byte_idx as u8).wrapping_mul(17))
                .wrapping_add(0x42);
        }
        deterministic_noncanonical[0] |= 0x80;

        for (variant, word) in [
            ("high-bit-minimum", high_bit),
            ("high-bit-pattern", deterministic_noncanonical),
        ] {
            let mut bad_proof = fixture.proof.clone();
            bad_proof[offset..offset + 0x20].copy_from_slice(&word);
            assert_deployed_call_rejects(
                &mut evm,
                &fixture,
                &bad_proof,
                &format!("{name} scalar replaced with {variant} at proof offset {offset}"),
            );
        }
    }
}

#[test]
fn representative_proof_section_mutations_are_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let sections = representative_proof_section_offsets(&fixture);
    assert!(
        !sections.is_empty(),
        "fixture should expose representative proof sections"
    );

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (section, offset) in sections {
        let mut bad_proof = fixture.proof.clone();
        bad_proof[offset] ^= 0x01;
        assert_deployed_call_rejects(
            &mut evm,
            &fixture,
            &bad_proof,
            &format!("mutated proof section `{section}` at proof offset {offset}"),
        );
    }
}

#[test]
fn separate_verifier_adversarial_calldata_variants_are_rejected() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let mut evm = deployed_separate_verifier(&fixture);
    let valid = encode_calldata(&fixture.proof, &fixture.instances);
    if !deployed_raw_call_accepts(&mut evm, valid.clone(), "valid separate-verifier calldata") {
        return;
    }

    let mut wrong_instances = fixture.instances.clone();
    wrong_instances[0] += F::ONE;
    assert_solidity_rejects(
        call_deployed_verifier(&mut evm, &fixture.proof, &wrong_instances),
        "wrong instance",
    );

    let r_be = fr_modulus_be_word();
    let mut noncanonical_instance = valid.clone();
    let instance_word_start = first_instance_word_start(&fixture.proof);
    noncanonical_instance[instance_word_start..instance_word_start + 0x20].copy_from_slice(&r_be);
    assert_solidity_rejects(
        call_deployed_verifier_raw(&mut evm, noncanonical_instance),
        "instance scalar equal to Fr modulus",
    );

    let mut endian_swapped_instance = valid.clone();
    let mut swapped_word: [u8; 32] = valid[instance_word_start..instance_word_start + 0x20]
        .try_into()
        .expect("instance word");
    swapped_word.reverse();
    if swapped_word == valid[instance_word_start..instance_word_start + 0x20] {
        swapped_word[31] ^= 0x01;
    }
    endian_swapped_instance[instance_word_start..instance_word_start + 0x20]
        .copy_from_slice(&swapped_word);
    assert_solidity_rejects(
        call_deployed_verifier_raw(&mut evm, endian_swapped_instance),
        "public input encoded with reversed endianness",
    );

    let mut trailing_bytes = valid.clone();
    trailing_bytes.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);

    let mut proof_head_overlap = valid.clone();
    overwrite_u256_word(&mut proof_head_overlap, 0x04, 0x20);

    let mut proof_head_shifted_without_gap = valid.clone();
    overwrite_u256_word(&mut proof_head_shifted_without_gap, 0x04, 0x60);

    let mut instances_head_overlap = valid.clone();
    overwrite_u256_word(&mut instances_head_overlap, 0x24, 0x40);

    let mut instances_head_shifted = valid.clone();
    overwrite_u256_word(
        &mut instances_head_shifted,
        0x24,
        canonical_instances_head(&fixture.proof) as u64 + 0x20,
    );

    let shifted_valid_abi = calldata_with_shifted_dynamic_heads(&valid, &fixture.proof);

    for (name, calldata) in [
        ("trailing bytes", trailing_bytes),
        ("proof head overlaps ABI head", proof_head_overlap),
        (
            "proof head shifted without matching gap",
            proof_head_shifted_without_gap,
        ),
        ("instances head overlaps proof", instances_head_overlap),
        ("instances head shifted", instances_head_shifted),
        (
            "valid ABI with noncanonical dynamic offsets",
            shifted_valid_abi,
        ),
    ] {
        assert_solidity_rejects(call_deployed_verifier_raw(&mut evm, calldata), name);
    }
}

#[test]
fn verifier_rejects_when_x_is_forced_to_domain_root() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let forced_x_verifier =
        verifier_source_with_x_forced_to_one(&fixture.separate_verifier_solidity);
    let mut evm = deploy_separate_verifier_from_sources(&forced_x_verifier, &fixture.vk_solidity);

    assert_solidity_rejects(
        call_deployed_verifier(&mut evm, &fixture.proof, &fixture.instances),
        "verifier with x forced to domain root should hit zero Lagrange denominator",
    );
}

#[test]
fn every_proof_g1_rejects_noncanonical_coordinates() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let layout = proof_g1_layout(&fixture);

    assert_eq!(
        layout.compressed_offsets.len(),
        layout.repacked_offsets.len(),
        "native/Solidity proof G1 offset schedules must agree"
    );

    let native_bad = [0xffu8; 48];
    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (idx, (&compressed_offset, &repacked_offset)) in
        layout.compressed_offsets.iter().zip(layout.repacked_offsets.iter()).enumerate()
    {
        let mut bad_native = fixture.compressed_proof.clone();
        bad_native[compressed_offset..compressed_offset + 48].copy_from_slice(&native_bad);
        assert_native_poseidon_rejects(
            &fixture,
            &bad_native,
            &format!("native noncanonical G1 idx={idx} compressed_offset={compressed_offset}"),
        );

        let mut bad_solidity = fixture.proof.clone();
        // EIP-2537 padded G1 words require the top 16 bytes of x_hi/y_hi
        // to be zero. Set one padding byte so the Solidity canonicality
        // guard must reject before the point can enter the transcript.
        bad_solidity[repacked_offset] = 1;
        assert_deployed_call_rejects(
            &mut evm,
            &fixture,
            &bad_solidity,
            &format!("Solidity noncanonical G1 idx={idx} repacked_offset={repacked_offset}"),
        );
    }
}

#[test]
fn every_proof_g1_rejects_base_modulus_coordinates() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let layout = proof_g1_layout(&fixture);
    let fq_modulus = bls_base_modulus_padded_coordinate();

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (idx, repacked_offset) in layout.repacked_offsets.iter().copied().enumerate() {
        for (coordinate, coordinate_offset) in [("x", 0usize), ("y", 0x40usize)] {
            let mut bad_proof = fixture.proof.clone();
            bad_proof
                [repacked_offset + coordinate_offset..repacked_offset + coordinate_offset + 64]
                .copy_from_slice(&fq_modulus);
            assert_deployed_call_rejects(
                &mut evm,
                &fixture,
                &bad_proof,
                &format!(
                    "Solidity G1 {coordinate} coordinate equal to Fq modulus idx={idx} \
                     repacked_offset={repacked_offset}"
                ),
            );
        }
    }
}

#[test]
fn every_proof_g1_rejects_off_curve_coordinates() {
    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let layout = proof_g1_layout(&fixture);
    let native_bad = compressed_off_curve_g1_bytes();
    let solidity_bad = eip2537_padded_off_curve_g1_bytes();

    let mut evm = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut evm, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    for (idx, (&compressed_offset, &repacked_offset)) in
        layout.compressed_offsets.iter().zip(layout.repacked_offsets.iter()).enumerate()
    {
        let mut bad_native = fixture.compressed_proof.clone();
        bad_native[compressed_offset..compressed_offset + 48].copy_from_slice(&native_bad);
        assert_native_poseidon_rejects(
            &fixture,
            &bad_native,
            &format!("native off-curve G1 idx={idx} compressed_offset={compressed_offset}"),
        );

        let mut bad_solidity = fixture.proof.clone();
        bad_solidity[repacked_offset..repacked_offset + 128].copy_from_slice(&solidity_bad);
        assert_deployed_call_rejects(
            &mut evm,
            &fixture,
            &bad_solidity,
            &format!("Solidity off-curve G1 idx={idx} repacked_offset={repacked_offset}"),
        );
    }
}

/// M-2 (docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md): a rejecting EIP-2537
/// precompile consumes ALL gas supplied to the STATICCALL, so before the
/// generated exact gas bounds a canonical-but-off-curve proof point burned
/// 63/64 of the transaction budget (measured 29.5M of a 30M limit). With the
/// bounds in place, rejecting a malformed point must cost no more than an
/// honest verification: the failing run is a prefix of the honest run plus
/// one precompile call whose forwarded gas is capped at its scheduled cost.
#[test]
fn malformed_proof_point_rejects_with_bounded_gas() {
    const GAS_LIMIT: u64 = 30_000_000;

    if !poseidon_inputs_available_for_evm() {
        return;
    }

    let fixture = create_property_poseidon_fixture();
    let layout = proof_g1_layout(&fixture);
    let solidity_bad = eip2537_padded_off_curve_g1_bytes();

    let mut deployed = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut deployed, &fixture, &fixture.proof, "valid proof") {
        return;
    }
    let honest_gas = match deployed.evm.try_call_with_gas(
        deployed.verifier_address,
        encode_calldata(&fixture.proof, &fixture.instances),
        GAS_LIMIT,
    ) {
        CallOutcome::Success { gas_used, .. } => gas_used,
        outcome => panic!("baseline honest verification failed: {outcome:?}"),
    };

    for (idx, repacked_offset) in layout.repacked_offsets.iter().copied().enumerate() {
        let mut bad_solidity = fixture.proof.clone();
        bad_solidity[repacked_offset..repacked_offset + 128].copy_from_slice(&solidity_bad);
        let gas_used = match deployed.evm.try_call_with_gas(
            deployed.verifier_address,
            encode_calldata(&bad_solidity, &fixture.instances),
            GAS_LIMIT,
        ) {
            CallOutcome::Revert { gas_used, .. } | CallOutcome::Halt { gas_used, .. } => gas_used,
            CallOutcome::Success { output, .. } => {
                // Rejection-by-return-false also must not burn the budget.
                assert_eq!(
                    output.last().copied(),
                    Some(0),
                    "off-curve G1 idx={idx} unexpectedly verified"
                );
                continue;
            }
        };
        assert!(
            gas_used <= honest_gas,
            "rejecting off-curve G1 idx={idx} repacked_offset={repacked_offset} burned \
             {gas_used} gas, more than the honest verification's {honest_gas}: a \
             precompile call site is forwarding more than its scheduled cost"
        );
    }
}

/// P4 (L-3, docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md): rejections revert
/// with a typed 4-byte custom-error selector so integrators can distinguish
/// failure classes. Decode three representative classes end-to-end.
#[test]
fn typed_errors_identify_rejection_classes() {
    use sha3::{Digest, Keccak256};

    if !poseidon_inputs_available_for_evm() {
        return;
    }
    let selector = |sig: &str| {
        let d = Keccak256::digest(sig.as_bytes());
        vec![d[0], d[1], d[2], d[3]]
    };

    let fixture = create_property_poseidon_fixture();
    let mut deployed = deployed_separate_verifier(&fixture);
    if !deployed_call_accepts(&mut deployed, &fixture, &fixture.proof, "valid proof") {
        return;
    }

    // (a) Trailing calldata byte -> BadCalldataShape (exact calldatasize pin;
    // documented ERC-2771 incompatibility).
    let mut trailing = encode_calldata(&fixture.proof, &fixture.instances);
    trailing.push(0);
    // (b) Non-canonical public instance (r) -> NonCanonicalScalar.
    let mut bad_instance = encode_calldata(&fixture.proof, &fixture.instances);
    let len = bad_instance.len();
    bad_instance[len - 32..].copy_from_slice(
        &hex::decode("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
            .expect("BLS12-381 r"),
    );
    // (c) Off-curve proof point -> BadPointEncoding is checked only for pad /
    // range violations; a canonical-but-off-curve point fails at the MSM, so
    // expect PrecompileFailed or ProofRejected there instead. Use a pad-byte
    // violation for the deterministic BadPointEncoding class.
    let layout = proof_g1_layout(&fixture);
    let mut bad_pad = fixture.proof.clone();
    bad_pad[layout.repacked_offsets[0]] = 1;
    let bad_pad = encode_calldata(&bad_pad, &fixture.instances);

    for (name, calldata, expected_sig) in [
        ("trailing calldata byte", trailing, "BadCalldataShape()"),
        (
            "non-canonical instance",
            bad_instance,
            "NonCanonicalScalar()",
        ),
        ("pad-byte violation", bad_pad, "BadPointEncoding()"),
    ] {
        match deployed.evm.try_call_with_gas(deployed.verifier_address, calldata, 30_000_000) {
            CallOutcome::Revert { output, .. } => {
                assert_eq!(
                    output,
                    selector(expected_sig),
                    "{name} must revert with {expected_sig}"
                );
            }
            outcome => panic!("{name} did not revert: {outcome:?}"),
        }
    }
}

/// H-1 provenance (docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md): the
/// production Midnight SRS assets must bind their `s_g2` — the element the
/// deployed verifier's `NEG_S_G2_BASE` is derived from — to the same tau
/// that generated their Lagrange basis. The build-time assert in
/// `src/lowering/vk.rs` runs this check on whatever `params` a build was
/// handed; this test runs it directly against the distributed asset files,
/// so a corrupted or substituted download fails here even before any build.
#[test]
fn midnight_srs_assets_bind_s_g2_to_lagrange_tau() {
    use ff::PrimeField;
    use midnight_zk_stdlib::utils::plonk_api::{load_srs, SrsSource};

    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping Midnight SRS tau-binding check: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return;
    }
    let srs_dir = srs_dir();
    env::set_var("SRS_DIR", &srs_dir);

    let mut checked = 0usize;
    for (asset, k) in [("midnight-srs-2p19", 19u32), ("midnight-srs-2p20", 20u32)] {
        if !PathBuf::from(&srs_dir).join(asset).exists() {
            eprintln!("skipping {asset}: not present under {srs_dir}");
            continue;
        }
        let params = load_srs(SrsSource::Midnight, k, 2);
        // omega for the 2^k evaluation domain the Lagrange basis is over.
        let omega =
            <F as PrimeField>::ROOT_OF_UNITY.pow_vartime([1u64 << (<F as PrimeField>::S - k)]);
        assert!(
            crate::lowering::vk::srs_tau_is_consistent(
                params.g_lagrange(),
                omega,
                params.s_g2().to_affine(),
            ),
            "{asset}: s_g2 does not correspond to the tau underlying g_lagrange; \
             the asset is corrupted or was substituted"
        );
        checked += 1;
    }
    if checked == 0 {
        eprintln!(
            "no midnight-srs assets found under {srs_dir}; \
             fetch them with scripts/run_ivc_bench.sh or record_srs_provenance.sh"
        );
    }
}

/// Produce a native Poseidon proof and verify it before Solidity tests use it.
fn generate_poseidon_proof(
    srs: &PoseidonParams,
    relation: &PoseidonExample,
    vk: &MidnightVK,
) -> (Vec<u8>, F) {
    let pk = midnight_zk_stdlib::setup_pk(relation, vk);
    let mut rng = ChaCha8Rng::seed_from_u64(42);
    let witness: [F; 3] = core::array::from_fn(|_| F::random(&mut rng));
    let instance = <PoseidonChip<F> as HashCPU<F, F>>::hash(&witness);
    let prover_rng = ChaCha8Rng::seed_from_u64(0xdebd);
    let proof = midnight_zk_stdlib::prove::<PoseidonExample, sha3::Keccak256>(
        srs, &pk, relation, &instance, witness, prover_rng,
    )
    .expect("proof generation should not fail");

    midnight_zk_stdlib::verify::<PoseidonExample, sha3::Keccak256>(
        &srs.verifier_params(),
        vk,
        &instance,
        None,
        &proof,
    )
    .expect("generated proof should verify natively");

    (proof, instance)
}

/// Property case: a valid Poseidon proof is accepted.
fn run_property_poseidon_positive_case(separate: bool, seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let mut deployed = deployed_property_poseidon_verifier(&fixture, separate);
    assert_deployed_call_accepts(
        &mut deployed,
        &fixture,
        &fixture.proof,
        &format!("valid proof seed={seed} separate={separate}"),
    );
}

/// Property case: mutating the public instance is rejected.
fn run_property_poseidon_wrong_instance_case(separate: bool, seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let mut deployed = deployed_property_poseidon_verifier(&fixture, separate);
    assert_deployed_call_accepts(
        &mut deployed,
        &fixture,
        &fixture.proof,
        &format!("valid proof before wrong-instance mutation seed={seed} separate={separate}"),
    );

    let mut bad_instances = fixture.instances.clone();
    bad_instances[0] += F::ONE;

    let output = call_deployed_verifier(&mut deployed, &fixture.proof, &bad_instances);
    assert_solidity_rejects(
        output,
        &format!("wrong instance seed={seed} separate={separate}"),
    );
}

/// Property case: flipping one proof bit is rejected.
fn run_property_poseidon_malleated_proof_case(separate: bool, seed: u64, bit_idx: usize) {
    let fixture = create_property_poseidon_fixture();
    let mut deployed = deployed_property_poseidon_verifier(&fixture, separate);
    assert_deployed_call_accepts(
        &mut deployed,
        &fixture,
        &fixture.proof,
        &format!("valid proof before proof mutation seed={seed} separate={separate}"),
    );

    let mut bad_proof = fixture.proof.clone();
    let byte_idx = bit_idx / 8 % bad_proof.len();
    let bit_mask = 1u8 << (bit_idx % 8);
    bad_proof[byte_idx] ^= bit_mask;

    let output = call_deployed_verifier(&mut deployed, &bad_proof, &fixture.instances);
    assert_solidity_rejects(
        output,
        &format!("malleated proof seed={seed} separate={separate}"),
    );
}

/// Property case: mutating the linked VK source prevents verification.
fn run_property_poseidon_wrong_vk_case(seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let mut baseline = deployed_separate_verifier(&fixture);
    assert_deployed_call_accepts(
        &mut baseline,
        &fixture,
        &fixture.proof,
        &format!("valid proof before wrong-vk mutation seed={seed}"),
    );

    let mutated_vk_solidity = mutate_first_large_hex_literal(&fixture.vk_solidity, seed as usize);
    assert_separate_verifier_rejects_vk_mutation(
        &fixture.separate_verifier_solidity,
        &mutated_vk_solidity,
        &fixture.proof,
        &fixture.instances,
        &format!("wrong vk seed={seed}"),
    );
}

/// Property case: changing only the VK digest literal breaks the pinned
/// verifier.
fn run_separate_vk_digest_prefix_affects_verification_case(seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let original = call_separate_verifier(
        &fixture.separate_verifier_solidity,
        &fixture.vk_solidity,
        &fixture.proof,
        &fixture.instances,
    );
    assert_solidity_accepts(original, &format!("valid separate vk seed={seed}"));

    assert_separate_verifier_rejects_vk_mutation(
        &fixture.separate_verifier_solidity,
        &mutate_vk_digest_literal_only(&fixture.vk_solidity),
        &fixture.proof,
        &fixture.instances,
        &format!("digest-only mutated separate vk seed={seed}"),
    );
}

/// Property case: start from valid calldata, then mutate one structured field
/// at a time so parser/layout bugs are exercised beyond blind byte flips.
fn run_structured_proof_calldata_mutation_case(seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let valid = encode_calldata(&fixture.proof, &fixture.instances);
    let mutations = structured_proof_calldata_mutations(&fixture, &valid, seed);
    assert!(
        !mutations.is_empty(),
        "structured calldata fuzzer must emit at least one mutation"
    );

    let mut deployed = deployed_separate_verifier(&fixture);
    if !deployed_raw_call_accepts(
        &mut deployed,
        valid.clone(),
        &format!("valid calldata before structured mutation fuzz seed={seed}"),
    ) {
        return;
    }

    for mutation in mutations {
        assert_solidity_rejects(
            call_deployed_verifier_raw(&mut deployed, mutation.calldata),
            &format!(
                "structured calldata mutation seed={seed}: {}",
                mutation.name
            ),
        );
    }
}

/// Property case: compare the typed proof calldata layout, proof repacker, and
/// rendered Yul reader so missing reads or offset drift fail before runtime.
fn run_proof_layout_repack_reader_case(seed: u64) {
    let fixture = create_property_poseidon_fixture();
    let layout = &fixture.proof_layout;
    let repack_plan =
        crate::lowering::quotient_numerator::vm::RepackedProofLayoutPlan::from_proof_layout(layout);

    assert_eq!(
        layout.proof_cptr,
        proof_payload_word_start(),
        "layout proof pointer must match the ABI bytes payload start"
    );
    assert_eq!(
        layout.proof_len,
        fixture.proof.len(),
        "layout proof length must match repacked proof bytes"
    );
    assert_eq!(
        layout.proof_end,
        instances_len_word_start(&fixture.proof),
        "layout proof end must land on the instances length word"
    );
    assert_eq!(
        repack_plan.repacked_len(),
        fixture.proof.len(),
        "repack proof length must match ProofCalldataLayout"
    );
    assert_eq!(
        repack_plan.compressed_len(),
        fixture.compressed_proof.len(),
        "native compressed proof length must match repack plan"
    );
    assert_eq!(
        fixture.scalar_layout.eval_offset,
        layout.evals.start - layout.proof_cptr,
        "eval scalar offset drift between repack plan and proof layout"
    );
    assert_eq!(
        fixture.scalar_layout.num_evals, layout.evals.item_count,
        "eval scalar count drift between repack plan and proof layout"
    );
    assert_eq!(
        fixture.scalar_layout.q_eval_offset,
        layout.q_evals.start - layout.proof_cptr,
        "q_eval scalar offset drift between repack plan and proof layout"
    );
    assert_eq!(
        fixture.scalar_layout.num_point_sets, layout.q_evals.item_count,
        "q_eval scalar count drift between repack plan and proof layout"
    );
    assert_eq!(
        proof_g1_layout(&fixture).repacked_offsets,
        proof_layout_g1_offsets(layout),
        "G1 proof offsets must be identical in the repacker and typed layout"
    );

    let sections = proof_layout_reader_sections(layout);
    proof_reader_sections_cover_exactly_once(layout, &sections).unwrap_or_else(|err| {
        panic!("ProofCalldataLayout sections must cover proof bytes exactly once: {err}")
    });
    assert_seeded_layout_drift_is_detected(seed, layout, &sections);
    assert_rendered_reader_matches_proof_layout(
        &fixture.separate_verifier_solidity,
        layout,
        fixture.instances.len(),
    );
}

/// Compile, deploy, and call an embedded-VK verifier.
fn call_embedded_verifier(
    verifier_solidity: &str,
    proof: &[u8],
    instances: &[F],
) -> Result<Vec<u8>, ()> {
    call_embedded_verifier_raw(verifier_solidity, encode_calldata(proof, instances))
}

/// Compile, deploy, and call an embedded-VK verifier with prebuilt calldata.
fn call_embedded_verifier_raw(verifier_solidity: &str, calldata: Vec<u8>) -> Result<Vec<u8>, ()> {
    let mut deployed = deploy_embedded_verifier_from_source(verifier_solidity);
    call_deployed_verifier_raw(&mut deployed, calldata)
}

/// Compile, deploy, and call a separate-VK verifier pair.
fn call_separate_verifier(
    verifier_solidity: &str,
    vk_solidity: &str,
    proof: &[u8],
    instances: &[F],
) -> Result<Vec<u8>, ()> {
    let mut deployed = deploy_separate_verifier_from_sources(verifier_solidity, vk_solidity);
    call_deployed_verifier(&mut deployed, proof, instances)
}

/// Assert a separate verifier constructor rejects a bad VK dependency.
fn assert_separate_verifier_rejects_vk_dependency(
    verifier_solidity: &str,
    vk_solidity: &str,
    context: &str,
) {
    let vk_creation_code = compile_solidity(vk_solidity);
    let verifier_creation_code = compile_solidity(verifier_solidity);
    let mut evm = Evm::default();
    let vk_address = evm.create(vk_creation_code);
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        evm.create_with_address_arg(verifier_creation_code, vk_address);
    }));
    assert!(
        result.is_err(),
        "separate verifier constructor accepted invalid VK dependency: {context}"
    );
}

/// Assert a pinned quotient verifier constructor rejects a bad dependency set.
fn assert_pinned_quotient_constructor_rejects(
    verifier_solidity: &str,
    vk_solidity: &str,
    quotient_solidity: &str,
    context: &str,
) {
    let verifier_creation_code = compile_solidity(verifier_solidity);
    let vk_creation_code = compile_solidity(vk_solidity);
    let quotient_creation_code = compile_solidity(quotient_solidity);
    assert_pinned_quotient_constructor_rejects_address_args(
        &verifier_creation_code,
        &vk_creation_code,
        &quotient_creation_code,
        context,
    );
}

/// Assert constructor rejection from already-compiled dependency bytecode.
fn assert_pinned_quotient_constructor_rejects_address_args(
    verifier_creation_code: &[u8],
    vk_arg_creation_code: &[u8],
    quotient_arg_creation_code: &[u8],
    context: &str,
) {
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let mut evm = Evm::default();
        let vk_address = evm.create(vk_arg_creation_code.to_vec());
        let quotient_address = evm.create(quotient_arg_creation_code.to_vec());
        evm.create_with_two_address_args(
            verifier_creation_code.to_vec(),
            vk_address,
            quotient_address,
        );
    }));
    assert!(
        result.is_err(),
        "pinned verifier constructor accepted invalid dependency: {context}"
    );
}

/// Deployed verifier state shared by call helpers.
struct DeployedVerifier {
    evm: Evm,
    verifier_address: revm::primitives::Address,
}

/// Deploy the cached separate verifier/VK fixture.
fn deployed_separate_verifier(fixture: &PropertyPoseidonFixture) -> DeployedVerifier {
    deploy_separate_verifier_from_sources(&fixture.separate_verifier_solidity, &fixture.vk_solidity)
}

/// Deploy either cached embedded or separate Poseidon verifier.
fn deployed_property_poseidon_verifier(
    fixture: &PropertyPoseidonFixture,
    separate: bool,
) -> DeployedVerifier {
    if separate {
        deployed_separate_verifier(fixture)
    } else {
        deploy_embedded_verifier_from_source(&fixture.embedded_verifier_solidity)
    }
}

/// Compile and deploy one embedded verifier source.
fn deploy_embedded_verifier_from_source(verifier_solidity: &str) -> DeployedVerifier {
    let mut evm = Evm::default();
    let verifier_address = evm.create(compile_solidity(verifier_solidity));
    DeployedVerifier {
        evm,
        verifier_address,
    }
}

/// Compile and deploy separate VK then verifier source.
fn deploy_separate_verifier_from_sources(
    verifier_solidity: &str,
    vk_solidity: &str,
) -> DeployedVerifier {
    let mut evm = Evm::default();
    let vk_address = evm.create(compile_solidity(vk_solidity));
    let verifier_address =
        evm.create_with_address_arg(compile_solidity(verifier_solidity), vk_address);
    DeployedVerifier {
        evm,
        verifier_address,
    }
}

/// Encode calldata and call an already deployed verifier.
fn call_deployed_verifier(
    deployed: &mut DeployedVerifier,
    proof: &[u8],
    instances: &[F],
) -> Result<Vec<u8>, ()> {
    call_deployed_verifier_raw(deployed, encode_calldata(proof, instances))
}

/// Call an already deployed verifier with prebuilt calldata.
fn call_deployed_verifier_raw(
    deployed: &mut DeployedVerifier,
    calldata: Vec<u8>,
) -> Result<Vec<u8>, ()> {
    match deployed
        .evm
        .try_call_with_gas(deployed.verifier_address, calldata, 5_000_000_000)
    {
        CallOutcome::Success { output, .. } => Ok(output),
        CallOutcome::Revert { gas_used, output } => {
            eprintln!(
                "verifier reverted with gas_used = {gas_used}, output = 0x{}",
                hex::encode(output)
            );
            Err(())
        }
        CallOutcome::Halt { gas_used, reason } => {
            panic!("verifier halted with gas_used = {gas_used}, reason = {reason}");
        }
    }
}

/// Return whether a deployed verifier accepts a proof, skipping on bad
/// baseline.
fn deployed_call_accepts(
    deployed: &mut DeployedVerifier,
    fixture: &PropertyPoseidonFixture,
    proof: &[u8],
    context: &str,
) -> bool {
    let output = call_deployed_verifier(deployed, proof, &fixture.instances);
    solidity_output_is_true_or_skip(output, context)
}

/// Assert a deployed verifier accepts a proof.
fn assert_deployed_call_accepts(
    deployed: &mut DeployedVerifier,
    fixture: &PropertyPoseidonFixture,
    proof: &[u8],
    context: &str,
) {
    let output = call_deployed_verifier(deployed, proof, &fixture.instances);
    assert_solidity_accepts(output, context);
}

/// Return whether a raw deployed call accepts, skipping on bad baseline.
fn deployed_raw_call_accepts(
    deployed: &mut DeployedVerifier,
    calldata: Vec<u8>,
    context: &str,
) -> bool {
    let output = call_deployed_verifier_raw(deployed, calldata);
    solidity_output_is_true_or_skip(output, context)
}

/// Interpret verifier output as `true`, or request that adversarial test skip.
fn solidity_output_is_true_or_skip(output: Result<Vec<u8>, ()>, context: &str) -> bool {
    let expected_true = [vec![0; 31], vec![1]].concat();
    match output {
        Ok(bytes) if bytes == expected_true => true,
        Ok(bytes) => {
            eprintln!(
                "skipping adversarial Solidity test: baseline `{context}` returned 0x{}",
                hex::encode(bytes)
            );
            false
        }
        Err(()) => {
            eprintln!(
                "skipping adversarial Solidity test: baseline `{context}` reverted or halted"
            );
            false
        }
    }
}

/// Assert a deployed verifier rejects a proof mutation.
fn assert_deployed_call_rejects(
    deployed: &mut DeployedVerifier,
    fixture: &PropertyPoseidonFixture,
    proof: &[u8],
    context: &str,
) {
    let output = call_deployed_verifier(deployed, proof, &fixture.instances);
    assert_solidity_rejects(output, context);
}

/// Assert a separate verifier rejects proofs under a mutated VK contract.
fn assert_separate_verifier_rejects_vk_mutation(
    verifier_solidity: &str,
    vk_solidity: &str,
    proof: &[u8],
    instances: &[F],
    context: &str,
) {
    let vk_creation_code = compile_solidity(vk_solidity);
    let verifier_creation_code = compile_solidity(verifier_solidity);
    let mut evm = Evm::default();
    let vk_address = evm.create(vk_creation_code);
    let verifier_address = match std::panic::catch_unwind(AssertUnwindSafe(|| {
        evm.create_with_address_arg(verifier_creation_code, vk_address)
    })) {
        Ok(address) => address,
        Err(_) => return,
    };
    let mut deployed = DeployedVerifier {
        evm,
        verifier_address,
    };
    assert_solidity_rejects(
        call_deployed_verifier(&mut deployed, proof, instances),
        context,
    );
}

/// Assert the native verifier also rejects a compressed proof mutation.
fn assert_native_poseidon_rejects(
    fixture: &PropertyPoseidonFixture,
    compressed_proof: &[u8],
    context: &str,
) {
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        midnight_zk_stdlib::verify::<PoseidonExample, sha3::Keccak256>(
            &fixture.params_verifier,
            &fixture.vk,
            &fixture.instances[0],
            None,
            compressed_proof,
        )
    }));

    if let Ok(Ok(())) = result {
        panic!("native verifier accepted malformed proof: {context}");
    }
}

#[derive(Clone, Debug)]
struct ProofG1Layout {
    compressed_offsets: Vec<usize>,
    repacked_offsets: Vec<usize>,
}

#[derive(Clone, Debug)]
struct CalldataMutation {
    name: String,
    calldata: Vec<u8>,
}

#[derive(Clone, Debug)]
struct ProofLayoutSection {
    name: String,
    start: usize,
    end: usize,
}

/// Return named proof sections in the order the generated reader consumes them.
fn proof_layout_reader_sections(
    layout: &crate::lowering::abi::ProofCalldataLayout,
) -> Vec<ProofLayoutSection> {
    let mut sections = Vec::new();
    for (phase, section) in layout.advice_phases.iter().enumerate() {
        push_proof_layout_section(
            &mut sections,
            format!("advice phase {phase}"),
            section.start,
            section.end(),
        );
    }
    push_proof_layout_section(
        &mut sections,
        "lookup multiplicities",
        layout.lookup_multiplicities.start,
        layout.lookup_multiplicities.end(),
    );
    push_proof_layout_section(
        &mut sections,
        "permutation products",
        layout.permutation_products.start,
        layout.permutation_products.end(),
    );
    for lookup in &layout.lookups {
        push_proof_layout_section(
            &mut sections,
            format!("lookup {} helpers", lookup.lookup),
            lookup.helpers.start,
            lookup.helpers.end(),
        );
        push_proof_layout_section(
            &mut sections,
            format!("lookup {} accumulator", lookup.lookup),
            lookup.accumulator.start,
            lookup.accumulator.end(),
        );
    }
    push_proof_layout_section(
        &mut sections,
        "trash",
        layout.trash.start,
        layout.trash.end(),
    );
    push_proof_layout_section(
        &mut sections,
        "quotient limbs",
        layout.quotient_limbs.start,
        layout.quotient_limbs.end(),
    );
    push_proof_layout_section(
        &mut sections,
        "evals",
        layout.evals.start,
        layout.evals.end(),
    );
    push_proof_layout_section(
        &mut sections,
        "f_com",
        layout.f_com.start,
        layout.f_com.end(),
    );
    push_proof_layout_section(
        &mut sections,
        "q_evals",
        layout.q_evals.start,
        layout.q_evals.end(),
    );
    push_proof_layout_section(&mut sections, "pi", layout.pi.start, layout.pi.end());
    sections
}

/// Push one section range into a proof layout checker plan.
fn push_proof_layout_section(
    sections: &mut Vec<ProofLayoutSection>,
    name: impl Into<String>,
    start: usize,
    end: usize,
) {
    sections.push(ProofLayoutSection {
        name: name.into(),
        start,
        end,
    });
}

/// Confirm the planned proof-reader sections cover each proof byte once.
fn proof_reader_sections_cover_exactly_once(
    layout: &crate::lowering::abi::ProofCalldataLayout,
    sections: &[ProofLayoutSection],
) -> Result<(), String> {
    let mut owners: Vec<Option<usize>> = vec![None; layout.proof_len];
    for (section_idx, section) in sections.iter().enumerate() {
        if section.start > section.end {
            return Err(format!(
                "{} has inverted range {}..{}",
                section.name, section.start, section.end
            ));
        }
        if section.start < layout.proof_cptr || section.end > layout.proof_end {
            return Err(format!(
                "{} escapes proof range: {}..{} outside {}..{}",
                section.name, section.start, section.end, layout.proof_cptr, layout.proof_end
            ));
        }
        let section_start = section.start - layout.proof_cptr;
        let section_end = section.end - layout.proof_cptr;
        for (byte, owner) in owners.iter_mut().enumerate().take(section_end).skip(section_start) {
            if let Some(previous_idx) = *owner {
                return Err(format!(
                    "{} byte {byte:#x} overlaps {}",
                    section.name, sections[previous_idx].name
                ));
            }
            *owner = Some(section_idx);
        }
    }
    if let Some(byte) = owners.iter().position(Option::is_none) {
        return Err(format!("proof byte {byte:#x} is not read by any section"));
    }
    Ok(())
}

/// Mutate one planned section boundary and assert the coverage checker notices.
fn assert_seeded_layout_drift_is_detected(
    seed: u64,
    layout: &crate::lowering::abi::ProofCalldataLayout,
    sections: &[ProofLayoutSection],
) {
    let non_empty = sections
        .iter()
        .enumerate()
        .filter_map(|(idx, section)| (section.start < section.end).then_some(idx))
        .collect::<Vec<_>>();
    let drift_idx = non_empty[choose_index(seed.rotate_left(7), non_empty.len())];
    let mut drifted = sections.to_vec();
    if seed & 1 == 0 {
        drifted[drift_idx].end -= 1;
    } else {
        drifted[drift_idx].end += 1;
    }
    assert!(
        proof_reader_sections_cover_exactly_once(layout, &drifted).is_err(),
        "seeded layout drift in {} was not detected",
        sections[drift_idx].name
    );
}

/// Return all G1 offsets in the Solidity-facing proof according to layout.
fn proof_layout_g1_offsets(layout: &crate::lowering::abi::ProofCalldataLayout) -> Vec<usize> {
    let mut offsets = Vec::new();
    for section in &layout.advice_phases {
        append_section_item_offsets(
            &mut offsets,
            layout,
            section.start,
            section.item_count,
            section.item_bytes,
        );
    }
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.lookup_multiplicities.start,
        layout.lookup_multiplicities.item_count,
        layout.lookup_multiplicities.item_bytes,
    );
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.permutation_products.start,
        layout.permutation_products.item_count,
        layout.permutation_products.item_bytes,
    );
    for lookup in &layout.lookups {
        append_section_item_offsets(
            &mut offsets,
            layout,
            lookup.helpers.start,
            lookup.helpers.item_count,
            lookup.helpers.item_bytes,
        );
        append_section_item_offsets(
            &mut offsets,
            layout,
            lookup.accumulator.start,
            lookup.accumulator.item_count,
            lookup.accumulator.item_bytes,
        );
    }
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.trash.start,
        layout.trash.item_count,
        layout.trash.item_bytes,
    );
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.quotient_limbs.start,
        layout.quotient_limbs.item_count,
        layout.quotient_limbs.item_bytes,
    );
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.f_com.start,
        layout.f_com.item_count,
        layout.f_com.item_bytes,
    );
    append_section_item_offsets(
        &mut offsets,
        layout,
        layout.pi.start,
        layout.pi.item_count,
        layout.pi.item_bytes,
    );
    offsets
}

/// Append proof-relative offsets for homogeneous section items.
fn append_section_item_offsets(
    offsets: &mut Vec<usize>,
    layout: &crate::lowering::abi::ProofCalldataLayout,
    start: usize,
    item_count: usize,
    item_bytes: usize,
) {
    offsets.extend((0..item_count).map(|idx| start - layout.proof_cptr + idx * item_bytes));
}

/// Confirm the generated Solidity reader literals agree with the layout.
fn assert_rendered_reader_matches_proof_layout(
    solidity: &str,
    layout: &crate::lowering::abi::ProofCalldataLayout,
    num_instances: usize,
) {
    assert!(
        solidity.contains(&format!(
            "PROOF_LEN_CPTR = {};",
            yul_hex(proof_len_word_start())
        )),
        "rendered constants must expose the proof length word pointer"
    );
    assert!(
        solidity.contains(&format!("PROOF_CPTR = {};", yul_hex(layout.proof_cptr))),
        "rendered constants must expose ProofCalldataLayout::proof_cptr"
    );
    assert!(
        solidity.contains(&format!(
            "NUM_INSTANCE_CPTR = {};",
            yul_hex(layout.proof_end)
        )),
        "rendered constants must expose ProofCalldataLayout::proof_end"
    );
    assert!(
        solidity.contains(&format!(
            "eq({}, calldataload(PROOF_LEN_CPTR))",
            yul_hex(layout.proof_len)
        )),
        "rendered proof length guard must use ProofCalldataLayout::proof_len"
    );
    assert!(
        solidity.contains(&format!(
            "eq({}, calldataload(NUM_INSTANCE_CPTR))",
            num_instances
        )),
        "rendered instance length guard must use fixture instance count"
    );

    let reader = rendered_proof_reader_block(solidity);
    assert_eq!(
        rendered_proof_reader_loop_lengths(reader),
        expected_reader_loop_lengths(layout),
        "generated proof reader loop lengths drifted from ProofCalldataLayout"
    );
    assert_eq!(
        rendered_proof_reader_increment_lengths(reader),
        expected_reader_increment_lengths(layout),
        "generated proof reader proof_cptr increments drifted from ProofCalldataLayout"
    );
    assert!(
        solidity.contains(
            "if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR)) { fail(ERR_BAD_CALLDATA_SHAPE) }"
        ),
        "generated proof reader must fail closed if proof_cptr drifts"
    );
}

/// Slice the rendered source down to the proof parser block.
fn rendered_proof_reader_block(solidity: &str) -> &str {
    let start = solidity
        .find("let proof_cptr := PROOF_CPTR")
        .expect("rendered verifier contains proof parser start");
    let end = solidity
        .find("if iszero(eq(proof_cptr, NUM_INSTANCE_CPTR))")
        .expect("rendered verifier contains proof parser end guard");
    &solidity[start..end]
}

/// Extract `for { let end := add(proof_cptr, N) }` lengths from Yul.
fn rendered_proof_reader_loop_lengths(reader: &str) -> Vec<usize> {
    const NEEDLE: &str = "for { let end := add(proof_cptr, ";
    let mut lengths = Vec::new();
    let mut rest = reader;
    while let Some(pos) = rest.find(NEEDLE) {
        let after = &rest[pos + NEEDLE.len()..];
        let close = after.find(')').expect("proof reader loop has a closing paren");
        lengths.push(parse_yul_usize(after[..close].trim()));
        rest = &after[close..];
    }
    lengths
}

/// Extract every rendered `proof_cptr` increment stride from the proof reader.
fn rendered_proof_reader_increment_lengths(reader: &str) -> Vec<usize> {
    const NEEDLE: &str = "proof_cptr := add(proof_cptr, ";
    let mut lengths = Vec::new();
    let mut rest = reader;
    while let Some(pos) = rest.find(NEEDLE) {
        let after = &rest[pos + NEEDLE.len()..];
        let close = after.find(')').expect("proof reader increment has a closing paren");
        lengths.push(parse_yul_usize(after[..close].trim()));
        rest = &after[close..];
    }
    lengths
}

/// Expected loop byte lengths in the generated proof reader.
fn expected_reader_loop_lengths(layout: &crate::lowering::abi::ProofCalldataLayout) -> Vec<usize> {
    let mut lengths =
        layout.advice_phases.iter().map(|section| section.byte_len).collect::<Vec<_>>();
    if layout.lookup_multiplicities.item_count != 0 {
        lengths.push(layout.lookup_multiplicities.byte_len);
    }
    if layout.permutation_products.item_count != 0 {
        lengths.push(layout.permutation_products.byte_len);
    }
    if !layout.lookups.is_empty() {
        lengths.extend(layout.lookups.iter().map(|lookup| lookup.helpers.byte_len));
    }
    if layout.trash.item_count != 0 {
        lengths.push(layout.trash.byte_len);
    }
    lengths.push(layout.quotient_limbs.byte_len);
    lengths.push(layout.evals.byte_len);
    lengths.push(layout.q_evals.byte_len);
    lengths
}

/// Expected `proof_cptr` increment strides in the generated proof reader.
fn expected_reader_increment_lengths(
    layout: &crate::lowering::abi::ProofCalldataLayout,
) -> Vec<usize> {
    let mut lengths = layout
        .advice_phases
        .iter()
        .map(|section| section.item_bytes)
        .collect::<Vec<_>>();
    if layout.lookup_multiplicities.item_count != 0 {
        lengths.push(layout.lookup_multiplicities.item_bytes);
    }
    if layout.permutation_products.item_count != 0 {
        lengths.push(layout.permutation_products.item_bytes);
    }
    if !layout.lookups.is_empty() {
        for lookup in &layout.lookups {
            lengths.push(lookup.helpers.item_bytes);
            lengths.push(lookup.accumulator.item_bytes);
        }
    }
    if layout.trash.item_count != 0 {
        lengths.push(layout.trash.item_bytes);
    }
    lengths.push(layout.quotient_limbs.item_bytes);
    lengths.push(layout.evals.item_bytes);
    lengths.push(layout.f_com.item_bytes);
    lengths.push(layout.q_evals.item_bytes);
    lengths.push(layout.pi.item_bytes);
    lengths
}

/// Render a Yul/Solidity integer literal the way the templates do.
fn yul_hex(value: usize) -> String {
    format!("0x{value:x}")
}

/// Parse a simple Yul integer literal.
fn parse_yul_usize(literal: &str) -> usize {
    literal
        .strip_prefix("0x")
        .map(|hex| usize::from_str_radix(hex, 16).expect("valid hex literal"))
        .unwrap_or_else(|| literal.parse().expect("valid decimal literal"))
}

/// Return ordinary evaluation scalar offsets in the Solidity-facing proof.
fn proof_eval_offsets(fixture: &PropertyPoseidonFixture) -> Vec<(String, usize)> {
    let layout = fixture.scalar_layout;
    let offsets = (0..layout.num_evals)
        .map(|idx| (format!("eval[{idx}]"), layout.eval_offset + idx * 0x20))
        .collect::<Vec<_>>();
    assert!(
        offsets.iter().all(|(_, offset)| offset + 0x20 <= fixture.proof.len()),
        "eval offsets must be inside the Solidity proof"
    );
    offsets
}

/// Return quotient-opening evaluation offsets in the Solidity-facing proof.
fn proof_q_eval_offsets(fixture: &PropertyPoseidonFixture) -> Vec<(String, usize)> {
    let layout = fixture.scalar_layout;
    let offsets = (0..layout.num_point_sets)
        .map(|idx| (format!("q_eval[{idx}]"), layout.q_eval_offset + idx * 0x20))
        .collect::<Vec<_>>();
    assert!(
        offsets.iter().all(|(_, offset)| offset + 0x20 <= fixture.proof.len()),
        "q_eval offsets must be inside the Solidity proof"
    );
    offsets
}

/// Return named scalar-word offsets in the Solidity-facing proof.
fn proof_scalar_offsets(fixture: &PropertyPoseidonFixture) -> Vec<(String, usize)> {
    let mut offsets = proof_eval_offsets(fixture);
    offsets.extend(proof_q_eval_offsets(fixture));
    offsets
}

/// Return compressed and repacked G1 offsets for proof mutation tests.
fn proof_g1_layout(fixture: &PropertyPoseidonFixture) -> ProofG1Layout {
    let prefix_g1_count = fixture.scalar_layout.eval_offset / 0x80;
    assert_eq!(
        fixture.scalar_layout.eval_offset % 0x80,
        0,
        "G1 prefix must end on a repacked G1 boundary"
    );

    let f_com_repacked_offset =
        fixture.scalar_layout.eval_offset + fixture.scalar_layout.num_evals * 0x20;
    let pi_repacked_offset =
        fixture.scalar_layout.q_eval_offset + fixture.scalar_layout.num_point_sets * 0x20;
    assert_eq!(
        fixture.scalar_layout.q_eval_offset,
        f_com_repacked_offset + 0x80,
        "q_eval block must follow f_com"
    );

    let mut repacked_offsets = (0..prefix_g1_count).map(|idx| idx * 0x80).collect::<Vec<_>>();
    repacked_offsets.push(f_com_repacked_offset);
    repacked_offsets.push(pi_repacked_offset);

    let f_com_compressed_offset = prefix_g1_count * 48 + fixture.scalar_layout.num_evals * 0x20;
    let pi_compressed_offset =
        f_com_compressed_offset + 48 + fixture.scalar_layout.num_point_sets * 0x20;
    let mut compressed_offsets = (0..prefix_g1_count).map(|idx| idx * 48).collect::<Vec<_>>();
    compressed_offsets.push(f_com_compressed_offset);
    compressed_offsets.push(pi_compressed_offset);

    assert!(
        compressed_offsets
            .iter()
            .all(|offset| offset + 48 <= fixture.compressed_proof.len()),
        "compressed G1 offsets must be inside the native proof"
    );
    assert!(
        repacked_offsets.iter().all(|offset| offset + 0x80 <= fixture.proof.len()),
        "repacked G1 offsets must be inside the Solidity proof"
    );

    ProofG1Layout {
        compressed_offsets,
        repacked_offsets,
    }
}

/// Find a canonical compressed x-coordinate that does not decode to a G1 point.
fn compressed_off_curve_g1_bytes() -> [u8; 48] {
    use group::GroupEncoding;
    use midnight_curves::G1Affine;

    for x in 1u64..10_000 {
        let mut candidate = [0u8; 48];
        candidate[40..48].copy_from_slice(&x.to_be_bytes());
        // BLS compressed flag, no infinity flag. The remaining high bits of
        // the x-coordinate are zero, so the coordinate is canonical.
        candidate[0] |= 0x80;

        let mut repr = <G1Affine as GroupEncoding>::Repr::default();
        repr.as_mut().copy_from_slice(&candidate);
        if bool::from(G1Affine::from_bytes(&repr).is_none()) {
            return candidate;
        }
    }

    panic!("failed to find a canonical compressed x-coordinate with no G1 point");
}

/// Return a padded uncompressed point that is canonical but off curve.
fn eip2537_padded_off_curve_g1_bytes() -> [u8; 128] {
    let mut out = [0u8; 128];
    // EIP-2537 padded uncompressed layout is x_hi, x_lo, y_hi, y_lo.
    // (0, 1) is field-canonical but not on BLS12-381 G1, whose affine
    // equation has b = 4, so the G1 precompiles must reject it.
    out[127] = 1;
    out
}

/// Assert a Solidity verifier call returned ABI-encoded true.
fn assert_solidity_accepts(output: Result<Vec<u8>, ()>, context: &str) {
    let expected_true = [vec![0; 31], vec![1]].concat();
    match output {
        Ok(bytes) => assert_eq!(bytes, expected_true, "{context}"),
        Err(()) => panic!("solidity call panicked unexpectedly: {context}"),
    }
}

/// Assert a Solidity verifier call reverted or halted.
fn assert_solidity_rejects(output: Result<Vec<u8>, ()>, context: &str) {
    assert!(
        output.is_err(),
        "invalid proof/calldata returned instead of reverting: {context}"
    );
}

/// Generate structured one-field mutations from a valid `verifyProof` calldata.
fn structured_proof_calldata_mutations(
    fixture: &PropertyPoseidonFixture,
    valid: &[u8],
    seed: u64,
) -> Vec<CalldataMutation> {
    let mut mutations = Vec::new();
    let proof_start = proof_payload_word_start();

    let g1_layout = proof_g1_layout(fixture);
    let g1_idx = choose_index(seed, g1_layout.repacked_offsets.len());
    let g1_offset = g1_layout.repacked_offsets[g1_idx];
    mutations.push(mutate_calldata_byte(
        valid,
        format!("proof G1[{g1_idx}] byte flip"),
        proof_start + g1_offset + choose_index(seed.rotate_left(7), 0x80),
        seed,
    ));

    let eval_offsets = proof_eval_offsets(fixture);
    let eval_idx = choose_index(seed.rotate_left(11), eval_offsets.len());
    let (eval_name, eval_offset) = &eval_offsets[eval_idx];
    mutations.push(mutate_calldata_byte(
        valid,
        format!("proof scalar {eval_name} byte flip"),
        proof_start + *eval_offset + choose_index(seed.rotate_left(13), 0x20),
        seed.rotate_left(17),
    ));

    let q_eval_offsets = proof_q_eval_offsets(fixture);
    let q_eval_idx = choose_index(seed.rotate_left(19), q_eval_offsets.len());
    let (q_eval_name, q_eval_offset) = &q_eval_offsets[q_eval_idx];
    mutations.push(mutate_calldata_byte(
        valid,
        format!("proof q_eval {q_eval_name} byte flip"),
        proof_start + *q_eval_offset + choose_index(seed.rotate_left(23), 0x20),
        seed.rotate_left(29),
    ));

    let instance_word_start = first_instance_word_start(&fixture.proof)
        + choose_index(seed.rotate_left(31), fixture.instances.len()) * 0x20;
    mutations.push(mutate_calldata_byte(
        valid,
        "public instance word byte flip",
        instance_word_start + choose_index(seed.rotate_left(37), 0x20),
        seed.rotate_left(41),
    ));

    let mut dynamic_head = valid.to_vec();
    if seed & 1 == 0 {
        overwrite_u256_word(&mut dynamic_head, 0x04, 0x20);
        mutations.push(CalldataMutation {
            name: "proof dynamic ABI head overlaps static head".to_string(),
            calldata: dynamic_head,
        });
    } else {
        overwrite_u256_word(
            &mut dynamic_head,
            0x24,
            canonical_instances_head(&fixture.proof) as u64 + 0x20,
        );
        mutations.push(CalldataMutation {
            name: "instances dynamic ABI head shifted away from proof tail".to_string(),
            calldata: dynamic_head,
        });
    }

    let mut trailing = valid.to_vec();
    let trailing_len = 1 + choose_index(seed.rotate_left(43), 0x20);
    trailing.extend(
        (0..trailing_len)
            .map(|idx| (seed as u8).wrapping_add(idx as u8).wrapping_mul(17).wrapping_add(1)),
    );
    mutations.push(CalldataMutation {
        name: format!("trailing bytes len={trailing_len}"),
        calldata: trailing,
    });

    let mut length_mutation = valid.to_vec();
    if seed & 2 == 0 {
        let proof_len = fixture.proof.len();
        let mutated_len = if seed & 4 == 0 {
            proof_len.saturating_sub(1)
        } else {
            proof_len + 0x20
        };
        overwrite_u256_word(
            &mut length_mutation,
            proof_len_word_start(),
            mutated_len as u64,
        );
        mutations.push(CalldataMutation {
            name: format!("proof length word changed to {mutated_len}"),
            calldata: length_mutation,
        });
    } else {
        let mutated_len = if seed & 4 == 0 {
            0
        } else {
            fixture.instances.len() + 1
        };
        overwrite_u256_word(
            &mut length_mutation,
            instances_len_word_start(&fixture.proof),
            mutated_len as u64,
        );
        mutations.push(CalldataMutation {
            name: format!("instances length word changed to {mutated_len}"),
            calldata: length_mutation,
        });
    }

    mutations.push(mutate_calldata_byte(
        valid,
        "function selector byte flip",
        choose_index(seed.rotate_left(47), FN_SIG_VERIFY_PROOF.len()),
        seed.rotate_left(53),
    ));

    let representative_offsets = representative_proof_section_offsets(fixture);
    let mut shifted_proof = fixture.proof.clone();
    let insertion_offset =
        representative_offsets[choose_index(seed.rotate_left(59), representative_offsets.len())].1;
    shifted_proof.splice(
        insertion_offset..insertion_offset,
        [0x80 | (seed as u8), seed.rotate_left(8) as u8],
    );
    mutations.push(CalldataMutation {
        name: format!("proof field offsets shifted at proof offset {insertion_offset}"),
        calldata: encode_calldata(&shifted_proof, &fixture.instances),
    });

    mutations
}

/// Pick a deterministic index from a fuzz seed.
fn choose_index(seed: u64, len: usize) -> usize {
    assert!(len != 0, "cannot choose from an empty set");
    seed as usize % len
}

/// Flip one non-zero bit in a calldata byte.
fn mutate_calldata_byte(
    valid: &[u8],
    name: impl Into<String>,
    byte_offset: usize,
    seed: u64,
) -> CalldataMutation {
    assert!(
        byte_offset < valid.len(),
        "calldata byte mutation offset {byte_offset} outside len {}",
        valid.len()
    );
    let mut calldata = valid.to_vec();
    calldata[byte_offset] ^= 1u8 << (seed as u8 & 7);
    CalldataMutation {
        name: name.into(),
        calldata,
    }
}

/// Flip one nibble in a large hex literal for broad source-mutation tests.
fn mutate_first_large_hex_literal(solidity: &str, ordinal_seed: usize) -> String {
    let bytes = solidity.as_bytes();
    let mut matches = Vec::new();
    for start in 0..bytes.len().saturating_sub(2) {
        if bytes[start] == b'0' && bytes[start + 1] == b'x' {
            let mut end = start + 2;
            while end < bytes.len() && bytes[end].is_ascii_hexdigit() {
                end += 1;
            }
            if end - (start + 2) >= 64 {
                matches.push((start, end));
            }
        }
    }

    assert!(
        !matches.is_empty(),
        "no 64-byte hex literal found to mutate"
    );
    let (start, end) = matches[ordinal_seed % matches.len()];
    let mut mutated = solidity.to_owned().into_bytes();
    let idx = end - 1 - ordinal_seed % ((end - start - 2).min(16));
    mutated[idx] = if mutated[idx] == b'0' { b'1' } else { b'0' };
    String::from_utf8(mutated).unwrap()
}

/// Mutate only the VK digest literal in rendered VK source.
fn mutate_vk_digest_literal_only(solidity: &str) -> String {
    mutate_value_hex_literal_on_line_containing(solidity, "vk_digest")
}

/// Mutate the value literal on the first rendered `mstore` line with `marker`.
fn mutate_value_hex_literal_on_line_containing(solidity: &str, marker: &str) -> String {
    let (line_start, line_end, _) = solidity
        .lines()
        .scan(0usize, |offset, line| {
            let start = *offset;
            *offset += line.len() + 1;
            Some((start, start + line.len(), line))
        })
        .find(|(_, _, line)| line.contains("mstore(") && line.contains(marker))
        .unwrap_or_else(|| panic!("mstore line marker not found: {marker}"));
    let line = &solidity[line_start..line_end];
    let line_before_comment = line.split_once("//").map(|(code, _)| code).unwrap_or(line);
    let bytes = line_before_comment.as_bytes();
    let mut value_literal = None;
    for start in 0..bytes.len().saturating_sub(1) {
        if bytes[start] != b'0' || bytes[start + 1] != b'x' {
            continue;
        }
        let mut end = start + 2;
        while end < bytes.len() && bytes[end].is_ascii_hexdigit() {
            end += 1;
        }
        if end - (start + 2) >= 64 {
            value_literal = Some((start + 2, end - (start + 2)));
        }
    }
    let (rel_hex_start, hex_len) =
        value_literal.unwrap_or_else(|| panic!("line `{marker}` missing value hex literal"));
    let abs_hex_start = line_start + rel_hex_start;

    let mut mutated = solidity.as_bytes().to_vec();
    let last = abs_hex_start + hex_len - 1;
    mutated[last] = if mutated[last] == b'0' { b'1' } else { b'0' };
    String::from_utf8(mutated).unwrap()
}

#[test]
fn vk_payload_mutator_targets_mstore_value_not_payload_offset() {
    let value = format!("0x{:064x}", 0u8);
    let old_shape = format!("mstore(0x0000, {value}) // vk_digest");
    let new_shape = format!("mstore(add(payload, 0x0000), {value}) // vk_digest");

    for source in [old_shape, new_shape] {
        let mutated = mutate_value_hex_literal_on_line_containing(&source, "vk_digest");
        assert!(
            mutated.contains("0x0000"),
            "payload offset should be left intact: {mutated}"
        );
        assert!(
            mutated.ends_with("0001) // vk_digest"),
            "mstore value should be mutated: {mutated}"
        );
    }
}

/// Replace one constructor smoke-test staticcall in rendered Solidity.
fn replace_required_precompile_staticcall(
    solidity: &str,
    needle: &str,
    replacement: &str,
) -> String {
    assert!(
        solidity.contains(needle),
        "required precompile smoke-test staticcall not found: {needle}"
    );
    solidity.replacen(needle, replacement, 1)
}

/// Create a proptest runner with fixture-friendly persistence settings.
fn new_property_test_runner() -> TestRunner {
    let cases = env::var("POSEIDON_PBT_CASES")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(3);
    TestRunner::new(ProptestConfig {
        cases,
        failure_persistence: None,
        ..ProptestConfig::default()
    })
}

/// Overwrite one ABI word with a small big-endian integer.
fn overwrite_u256_word(bytes: &mut [u8], start: usize, value: u64) {
    bytes[start..start + 32].fill(0);
    bytes[start + 24..start + 32].copy_from_slice(&value.to_be_bytes());
}

/// Return the BLS12-381 scalar-field modulus as one big-endian word.
fn fr_modulus_be_word() -> [u8; 32] {
    hex::decode("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
        .expect("fr modulus hex")
        .try_into()
        .expect("Fr modulus is one word")
}

/// Return the BLS12-381 scalar-field modulus as U256.
fn fr_modulus_u256() -> U256 {
    U256::from_be_bytes(fr_modulus_be_word())
}

/// Return the BLS12-381 base-field modulus in padded EIP-2537 coordinate form.
fn bls_base_modulus_padded_coordinate() -> [u8; 64] {
    let fq = hex::decode(
        "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f624\
         1eabfffeb153ffffb9feffffffffaaab",
    )
    .expect("Fq modulus hex");
    assert_eq!(fq.len(), 48, "BLS12-381 Fq modulus must be 48 bytes");

    let mut out = [0u8; 64];
    out[16..64].copy_from_slice(&fq);
    out
}

/// ABI-encode a single `bytes` argument call.
fn encode_bytes_call(signature: &str, payload: &[u8]) -> Vec<u8> {
    let padding = (32 - payload.len() % 32) % 32;
    let mut out = Vec::with_capacity(4 + 0x40 + payload.len() + padding);
    out.extend_from_slice(&sha3::Keccak256::digest(signature)[..4]);
    out.extend_from_slice(&u256_word(0x20));
    out.extend_from_slice(&u256_word(payload.len() as u64));
    out.extend_from_slice(payload);
    out.resize(out.len() + padding, 0);
    out
}

/// Append a named proof section offset if that offset is not already covered.
fn push_unique_section(
    sections: &mut Vec<(String, usize)>,
    name: impl Into<String>,
    offset: usize,
) {
    if sections.iter().all(|(_, existing)| *existing != offset) {
        sections.push((name.into(), offset));
    }
}

/// Return representative offsets spanning all major proof sections.
fn representative_proof_section_offsets(fixture: &PropertyPoseidonFixture) -> Vec<(String, usize)> {
    let layout = fixture.scalar_layout;
    assert!(
        layout.eval_offset >= 0x80,
        "fixture proof should contain at least one leading G1 commitment"
    );

    let mut sections = Vec::new();
    push_unique_section(&mut sections, "first transcript commitment", 0);
    push_unique_section(
        &mut sections,
        "last quotient limb commitment",
        layout.eval_offset - 0x80,
    );
    if layout.num_evals != 0 {
        push_unique_section(
            &mut sections,
            "first main evaluation scalar",
            layout.eval_offset,
        );
        push_unique_section(
            &mut sections,
            "last main evaluation scalar",
            layout.eval_offset + (layout.num_evals - 1) * 0x20,
        );
    }

    let f_com_offset = layout.eval_offset + layout.num_evals * 0x20;
    push_unique_section(&mut sections, "KZG f_com commitment", f_com_offset);

    if layout.num_point_sets != 0 {
        push_unique_section(
            &mut sections,
            "first KZG point-set evaluation scalar",
            layout.q_eval_offset,
        );
        push_unique_section(
            &mut sections,
            "last KZG point-set evaluation scalar",
            layout.q_eval_offset + (layout.num_point_sets - 1) * 0x20,
        );
    }

    push_unique_section(
        &mut sections,
        "KZG proof commitment pi",
        layout.q_eval_offset + layout.num_point_sets * 0x20,
    );

    assert!(
        sections.iter().all(|(_, offset)| *offset < fixture.proof.len()),
        "representative proof section offsets must be inside the proof"
    );
    sections
}

/// Patch rendered Solidity so the x challenge is forced to one.
fn verifier_source_with_x_forced_to_one(solidity: &str) -> String {
    let needle = "buf_len := squeeze_to(buf_len, X_MPTR)";
    assert_eq!(
        solidity.matches(needle).count(),
        1,
        "expected exactly one x challenge squeeze to patch"
    );
    solidity.replacen(
        needle,
        "buf_len := squeeze_to(buf_len, X_MPTR)\n            mstore(X_MPTR, 1)",
        1,
    )
}

/// Canonical ABI head offset for the `instances` dynamic argument.
fn canonical_instances_head(proof: &[u8]) -> usize {
    0x40 + 0x20 + proof.len()
}

/// Calldata byte offset of the proof length word.
fn proof_len_word_start() -> usize {
    4 + 0x40
}

/// Calldata byte offset of the first proof payload word.
fn proof_payload_word_start() -> usize {
    proof_len_word_start() + 0x20
}

/// Calldata byte offset of the instance array length word.
fn instances_len_word_start(proof: &[u8]) -> usize {
    4 + canonical_instances_head(proof)
}

/// Calldata byte offset of the first instance word.
fn first_instance_word_start(proof: &[u8]) -> usize {
    instances_len_word_start(proof) + 0x20
}

/// Build malformed calldata with valid payloads but shifted dynamic heads.
fn calldata_with_shifted_dynamic_heads(valid: &[u8], proof: &[u8]) -> Vec<u8> {
    let mut shifted = valid.to_vec();
    shifted.splice(4 + 0x40..4 + 0x40, [0u8; 0x20]);
    overwrite_u256_word(&mut shifted, 0x04, 0x60);
    overwrite_u256_word(
        &mut shifted,
        0x24,
        canonical_instances_head(proof) as u64 + 0x20,
    );
    shifted
}

/// Return whether Poseidon EVM tests have all host prerequisites.
fn poseidon_inputs_available_for_evm() -> bool {
    if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
        eprintln!("skipping Poseidon Solidity property test: set {RUN_EVM_TESTS_ENV}=1 to run it");
        return false;
    }
    // Past this point the gate was explicitly requested, so a missing
    // prerequisite is a failure rather than a skip. Returning `false` here
    // would report a green run that compiled no Solidity and executed no
    // proof -- the failure mode that let the rendered fixture artifacts drift
    // out of date across several commits without any test noticing.
    poseidon_srs_available();
    solc_available();
    true
}

/// Parse common truthy environment flag values.
fn env_flag_enabled(name: &str) -> bool {
    env::var(name)
        .map(|value| {
            matches!(
                value.to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
        .unwrap_or(false)
}

/// Load the Poseidon test SRS for the feature set this crate was built with.
///
/// `outer-single-h-commitment` forwards `single-h-commitment` to
/// `midnight-proofs` but deliberately *not* to `midnight-zk-stdlib` (see the
/// feature comment in `Cargo.toml`: recursive proofs checked inside the decider
/// circuit stay on the multi-limb layout). The consequence is that
/// `srs_for_test` cannot be used under that feature: it calls `load_srs`, which
/// decides whether to extend the monomial basis from *zk-stdlib's own*
/// `single-h-commitment` setting. With the feature off there, `load_srs`
/// returns a plain `2^k`-element SRS, while the prover -- compiled from
/// `midnight-proofs` *with* the feature -- commits to one full-degree quotient
/// polynomial and needs `k + ceil(log2(cs_degree - 1))` monomial powers. The
/// mismatch surfaces as `SrsError(64, 252)` at proof generation, i.e. long
/// after the VK builds cleanly at `k`.
///
/// Mirror `load_srs`'s single-h branch here instead, so `--all-features` is a
/// working configuration rather than one that fails inside the prover.
/// `tests/ivc_keccak_solidity.rs` already does the same thing for the decider
/// proof (`outer_single_h_extended_srs_k`); this is that pattern applied to the
/// Poseidon property fixtures.
fn poseidon_srs_for_test(relation: &PoseidonExample) -> PoseidonParams {
    #[cfg(not(feature = "outer-single-h-commitment"))]
    {
        srs_for_test(relation, Some(POSEIDON_K))
    }
    #[cfg(feature = "outer-single-h-commitment")]
    {
        let cs_degree = cost_model(relation, Some(POSEIDON_K)).max_deg;
        // Same exponent `load_srs` uses: enough monomial powers to hold the
        // unsplit quotient polynomial.
        let extended_k = POSEIDON_K + ((cs_degree - 1) as f64).log2().ceil() as u32;
        let base = load_srs(SrsSource::Filecoin, POSEIDON_K, cs_degree);
        let extended = load_srs(SrsSource::Filecoin, extended_k, cs_degree);
        base.with_extended_monomial(extended)
    }
}

/// Require the Poseidon test SRS on disk.
///
/// Only called once the EVM gate has been explicitly requested, so a missing
/// asset panics with fetch instructions instead of silently skipping.
fn poseidon_srs_available() {
    let srs_dir = PathBuf::from(srs_dir());
    let exact_srs_path = srs_dir.join(format!("bls_filecoin_2p{POSEIDON_K}"));
    let fallback_srs_path = srs_dir.join("bls_filecoin_2p19");
    assert!(
        exact_srs_path.exists() || fallback_srs_path.exists(),
        "{RUN_EVM_TESTS_ENV}=1 requires the test SRS, but it was not found at {} or {}.\n\
         Fetch it with:\n    curl -L -o {} {SRS_DOWNLOAD_URL}\n\
         or point SRS_DIR at an existing copy.",
        exact_srs_path.display(),
        fallback_srs_path.display(),
        fallback_srs_path.display(),
    );
}

/// Require the pinned solc.
///
/// Same contract as [`poseidon_srs_available`]: loud once the gate is on.
fn solc_available() {
    assert!(
        pinned_solc_available(),
        "{RUN_EVM_TESTS_ENV}=1 requires solc {}, which was not found or did not match.\n\
         Install it, point SOLC at the binary, or set {}=1 to accept another version.",
        crate::PINNED_SOLC_VERSION,
        crate::ALLOW_UNPINNED_SOLC_ENV,
    );
}

/// Resolve the SRS directory used by fixture setup.
fn srs_dir() -> String {
    if let Ok(dir) = env::var("SRS_DIR") {
        return dir;
    }

    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../zk_stdlib/examples/assets")
        .to_string_lossy()
        .into_owned()
}

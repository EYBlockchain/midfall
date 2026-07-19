// SPDX-License-Identifier: CC0-1.0
//! Lowering regression tests.
//!
//! These tests pin layout constants, template contracts, generated Yul
//! structure, and compact quotient VM invariants so the reorganization remains
//! behavior-preserving.

use std::collections::HashMap;

use ff::{Field, PrimeField};
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Constraints,
        Error as PlonkError, Expression, FirstPhase, Selector, VerifyingKey,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use ruint::aliases::U256;

use super::{
    config::{
        DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES, DEFAULT_QUOTIENT_LIMB_VM_OPS,
        DEFAULT_QUOTIENT_NATIVE_GATES,
    },
    encoding::*,
    kzg,
    layout::{self, WORD_BYTES},
    quotient_numerator::vm::*,
    VerifierBuildInputs,
};
use crate::{
    api::{
        AccumulatorEncoding, CommittedInstanceCommitmentKind, GeneratorConfig, GeneratorError,
        QuotientIdentityManifestTarget, QuotientIdentitySource,
    },
    SolidityGenerator,
};

/// Solidity/Yul template corpus scanned by documentation and regression tests.
const VERIFIER_TEMPLATE_CORPUS: &str = concat!(
    include_str!("../../templates/contracts/Halo2Verifier.sol"),
    "\n",
    include_str!("../../templates/partials/verifier/Constants.sol"),
    "\n",
    include_str!("../../templates/partials/verifier/PrecompileSmoke.sol"),
    "\n",
    include_str!("../../templates/partials/verifier/Constructors.sol"),
    "\n",
    include_str!("../../templates/partials/verifier/AssemblyHelpers.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/AccumulatorHelpers.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/TraceAndGasHelpers.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/VkLoading.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/TranscriptProofParser.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/Lagrange.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/QuotientAndLinearization.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/Pcs.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/FinalPairing.yul"),
    "\n",
    include_str!("../../templates/partials/verifier/TraceReturn.yul"),
    "\n",
    include_str!("../../templates/partials/quotient_numerator/QuotientHelpers.yul"),
    "\n",
    include_str!("../../templates/partials/quotient_numerator/QuotientNumeratorBlock.yul"),
);

/// Production lowering sources scanned for required comment/documentation text.
const LOWERING_SOURCE_CORPUS: &str = concat!(
    include_str!("../builder/mod.rs"),
    "\n",
    include_str!("../builder/api.rs"),
    "\n",
    include_str!("../builder/render.rs"),
    "\n",
    include_str!("../builder/repack.rs"),
    "\n",
    include_str!("artifacts.rs"),
    "\n",
    include_str!("diagnostics.rs"),
    "\n",
    include_str!("plan.rs"),
    "\n",
    include_str!("quotient.rs"),
    "\n",
    include_str!("vk.rs"),
);

/// Source corpus used to keep stale module names out of the public crate.
const MODULE_RENAME_SOURCE_CORPUS: &str = concat!(
    include_str!("../lib.rs"),
    "\n",
    include_str!("../api.rs"),
    "\n",
    include_str!("../evm.rs"),
    "\n",
    include_str!("../builder/mod.rs"),
    "\n",
    include_str!("../builder/api.rs"),
    "\n",
    include_str!("../builder/render.rs"),
    "\n",
    include_str!("../builder/repack.rs"),
    "\n",
    include_str!("mod.rs"),
    "\n",
    include_str!("artifacts.rs"),
    "\n",
    include_str!("calldata.rs"),
    "\n",
    include_str!("diagnostics.rs"),
    "\n",
    include_str!("plan.rs"),
    "\n",
    include_str!("quotient.rs"),
    "\n",
    include_str!("vk.rs"),
);

/// Lowering-only corpus used to enforce no dependency on the builder facade.
const LOWERING_ONLY_SOURCE_CORPUS: &str = concat!(
    include_str!("mod.rs"),
    "\n",
    include_str!("artifacts.rs"),
    "\n",
    include_str!("calldata.rs"),
    "\n",
    include_str!("diagnostics.rs"),
    "\n",
    include_str!("plan.rs"),
    "\n",
    include_str!("quotient.rs"),
    "\n",
    include_str!("vk.rs"),
);

/// Return the concatenated verifier template corpus.
fn verifier_template_corpus() -> &'static str {
    VERIFIER_TEMPLATE_CORPUS
}

/// Return the concatenated production lowering source corpus.
fn lowering_source_corpus() -> &'static str {
    LOWERING_SOURCE_CORPUS
}

#[test]
fn module_rename_boundaries_stay_clean() {
    for stale in [
        concat!("crate::", "codegen"),
        concat!("crate::", "generator"),
        concat!("mod ", "codegen"),
        concat!("mod ", "generator"),
    ] {
        assert!(
            !MODULE_RENAME_SOURCE_CORPUS.contains(stale),
            "source should not refer to stale module path `{stale}`"
        );
    }
    assert!(
        !LOWERING_ONLY_SOURCE_CORPUS.contains(concat!("crate::", "builder")),
        "lowering must not depend on the builder facade"
    );
}

#[derive(Default)]
struct TestQuotientExpressionEnv {
    fixed: HashMap<(usize, i32), QuotientExpr>,
    advice: HashMap<(usize, i32), QuotientExpr>,
    instance: HashMap<(usize, i32), QuotientExpr>,
    challenges: HashMap<usize, QuotientExpr>,
}

impl QuotientExpressionEnv for TestQuotientExpressionEnv {
    /// Test expressions should already have selector handling resolved.
    fn selector(&self, _selector: Selector) -> QuotientExpr {
        panic!("test expression should not contain selectors")
    }

    /// Return a fixed-column expression fixture.
    fn fixed(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        self.fixed[&(column_index, rotation)].clone()
    }

    /// Return an advice-column expression fixture.
    fn advice(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        self.advice[&(column_index, rotation)].clone()
    }

    /// Return an instance-column expression fixture.
    fn instance(&self, column_index: usize, rotation: i32) -> QuotientExpr {
        self.instance[&(column_index, rotation)].clone()
    }

    /// Return a challenge expression fixture.
    fn challenge(&self, index: usize) -> QuotientExpr {
        self.challenges[&index].clone()
    }
}

#[derive(Clone, Debug)]
struct LoweringPlanTestConfig {
    advice: Column<Advice>,
    selector: Selector,
}

#[derive(Clone, Debug, Default)]
struct LoweringPlanTestCircuit;

impl Circuit<Fq> for LoweringPlanTestCircuit {
    /// Config columns for the synthetic lowering-plan circuit.
    type Config = LoweringPlanTestConfig;
    /// Simple floor planner is enough for the one-row fixture.
    type FloorPlanner = SimpleFloorPlanner;
    /// The fixture circuit has no extra parameters.
    type Params = ();

    /// Return an empty witness copy of the fixture.
    fn without_witnesses(&self) -> Self {
        Self
    }

    /// Configure a tiny circuit that still exercises both instance columns.
    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let advice = meta.advice_column();
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();
        let selector = meta.selector();

        meta.create_gate("lowering plan balance", |meta| {
            let advice = meta.query_advice(advice, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());
            Constraints::with_selector(
                selector,
                vec![(
                    "lowering plan balance",
                    advice + committed + public - Expression::Constant(Fq::from(7u64)),
                )],
            )
        });

        LoweringPlanTestConfig { advice, selector }
    }

    /// Assign the single row consumed by the balance gate.
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        layouter.assign_region(
            || "lowering plan row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(
                    || "advice",
                    config.advice,
                    0,
                    || Value::known(Fq::from(7u64)),
                )?;
                Ok(())
            },
        )
    }
}

/// Generate parameters and VK for lowering-plan integration tests.
fn lowering_plan_test_vk() -> (
    ParamsKZG<Bls12>,
    VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
) {
    let mut rng = ChaCha8Rng::seed_from_u64(7);
    let params = ParamsKZG::<Bls12>::unsafe_setup(4, &mut rng);
    let circuit = LoweringPlanTestCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 4)
        .expect("test circuit VK should build");
    (params, vk)
}

#[derive(Clone, Debug)]
struct RotatedPublicInstanceCircuit;

impl Circuit<Fq> for RotatedPublicInstanceCircuit {
    type Config = ();
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let advice = meta.advice_column();
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();

        meta.create_gate("rotated public instance", |meta| {
            let advice = meta.query_advice(advice, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public_next = meta.query_instance(public_instance, Rotation::next());
            Constraints::without_selector(vec![(
                "rotated public instance",
                advice + committed + public_next,
            )])
        });
    }

    fn synthesize(
        &self,
        _config: Self::Config,
        _layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        Ok(())
    }
}

#[test]
fn generator_rejects_rotated_non_committed_instance_queries() {
    let mut rng = ChaCha8Rng::seed_from_u64(8);
    let params = ParamsKZG::<Bls12>::unsafe_setup(4, &mut rng);
    let circuit = RotatedPublicInstanceCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 4)
        .expect("test circuit VK should build");

    assert!(matches!(
        SolidityGenerator::try_new(&params, &vk, GeneratorConfig::new(1, 1)),
        Err(GeneratorError::RotatedInstanceQuery {
            column: 1,
            rotation: 1,
        })
    ));
}

/// Declares two advice columns but queries only one, so the second is absorbed
/// into the transcript without ever being opened by a PCS query.
struct UnopenedAdviceColumnCircuit;

impl Circuit<Fq> for UnopenedAdviceColumnCircuit {
    type Config = ();
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let advice = meta.advice_column();
        // Declared and committed, but never queried: this is the shape
        // `ProtocolPlan::validate` rejects.
        let _unopened = meta.advice_column();
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();

        meta.create_gate("unopened advice", |meta| {
            let advice = meta.query_advice(advice, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());
            Constraints::without_selector(vec![("unopened advice", advice + committed + public)])
        });
    }

    fn synthesize(
        &self,
        _config: Self::Config,
        _layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        Ok(())
    }
}

/// `try_new` documents a typed error for unsupported constraint systems, so an
/// unopened advice column must not reach the `panic!` inside
/// `ProtocolPlan::from_constraint_system`.
#[test]
fn generator_reports_unopened_advice_column_as_typed_error() {
    let mut rng = ChaCha8Rng::seed_from_u64(8);
    let params = ParamsKZG::<Bls12>::unsafe_setup(4, &mut rng);
    let circuit = UnopenedAdviceColumnCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 4)
        .expect("test circuit VK should build");

    let err = SolidityGenerator::try_new(&params, &vk, GeneratorConfig::new(1, 1))
        .expect_err("unopened advice column is outside the supported verifier shape");
    let GeneratorError::Planning { stage, message } = err else {
        panic!("expected a planning error, got {err:?}");
    };
    assert_eq!(stage, "constraint system");
    assert!(
        message.contains("absorbed but never opened"),
        "error should name the unopened advice column, got {message}"
    );
}

#[test]
fn scalar_le_to_be_word_reverses_exactly_one_word() {
    let mut le = [0u8; 32];
    le[0] = 0x01;
    le[1] = 0x23;
    le[30] = 0xab;
    le[31] = 0xcd;

    let be = scalar_le_to_be_word(&le);
    assert_eq!(be[0], 0xcd);
    assert_eq!(be[1], 0xab);
    assert_eq!(be[30], 0x23);
    assert_eq!(be[31], 0x01);
}

#[test]
fn external_quotient_frame_covers_vk_and_eval_memory() {
    let frame =
        VerifierBuildInputs::quotient_external_frame_from_bounds(0x1000, 0x300, 0x1400, 7, 3);
    assert_eq!(frame.frame_base, 0x1000);
    assert_eq!(frame.frame_len, 0x4e0);
    assert_eq!(frame.output_len, 0xa0);
    assert_eq!(frame.magic, QUOTIENT_EXTERNAL_MAGIC);
}

#[test]
fn external_quotient_output_uses_planned_return_buffer() {
    let verifier_template = verifier_template_corpus();
    assert!(
        verifier_template.contains("QUOTIENT_RETURN_MPTR"),
        "main verifier should name the planned external quotient return buffer"
    );
    assert!(
        verifier_template.contains("let q_out := QUOTIENT_RETURN_MPTR"),
        "external quotient staticcall output must not alias selector accumulators"
    );
    assert!(
            !verifier_template.contains("let q_out := SELECTOR_ACC_MPTR"),
            "selector accumulators model only selector buckets, not the two-word quotient return header"
        );
}

/// The Lagrange denominator run grows with `num_instances`, so an oversized
/// instance count must be rejected at construction with a typed error rather
/// than surfacing later as a memory-layout failure.
#[test]
fn generator_rejects_instance_counts_that_overrun_the_lagrange_run() {
    let (params, vk) = lowering_plan_test_vk();
    let meta = ConstraintSystemMeta::new(vk.cs(), 1);
    let rotation_last_words = meta.rotation_last.unsigned_abs() as usize;
    let max_num_instances =
        crate::lowering::layout::theta_window::LAGRANGE_RUN_CAP_WORDS - rotation_last_words - 1;

    SolidityGenerator::try_new(&params, &vk, GeneratorConfig::new(max_num_instances, 1))
        .expect("the largest fitting instance count must still be accepted");

    let err =
        SolidityGenerator::try_new(&params, &vk, GeneratorConfig::new(max_num_instances + 1, 1))
            .expect_err("one instance past the cap must be rejected");
    assert!(
        matches!(
            err,
            GeneratorError::TooManyInstances {
                max_num_instances: reported,
                ..
            } if reported == max_num_instances
        ),
        "unexpected error: {err:?}"
    );
}

#[test]
fn lowering_plan_reuses_stable_layout_facts() {
    let (params, vk) = lowering_plan_test_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let inputs = generator.inputs();

    let plan = inputs.lowering_plan();
    let repeated = inputs.lowering_plan();

    assert_eq!(plan.vk_mptr, repeated.vk_mptr);
    assert_eq!(plan.vk.runtime_bytes(), repeated.vk.runtime_bytes());
    plan.vk
        .validate_payload_layout()
        .expect("planned VK payload layout should validate");
    plan.memory.validate().expect("planned verifier memory should validate");
    assert_eq!(plan.memory.vk_mptr, plan.vk_mptr);
    assert_eq!(
        plan.pcs_memory_requirements,
        kzg::memory_requirements(&plan.meta, &plan.data)
    );

    let repack = plan.repacked_proof_layout_plan();
    assert_eq!(repack.repacked_len(), plan.proof_layout.proof_len);
    assert_eq!(repack.num_evals, plan.proof_layout.evals.item_count);
    assert_eq!(repack.num_point_sets, plan.proof_layout.q_evals.item_count);

    assert_eq!(plan.quotient.program.len, plan.quotient.build.bytes.len());
    assert!(plan.quotient.build.consts.len() <= plan.vk.quotient_const_words);
    assert_eq!(plan.quotient.program.stack_mptr, plan.quotient.stack_mptr);
    let quotient_stack_region = plan
        .memory
        .map
        .region("quotient_stack")
        .expect("quotient stack region should be registered");
    assert_eq!(quotient_stack_region.start, plan.quotient.stack_mptr);
    assert!(
        quotient_stack_region.len >= plan.quotient.build.max_stack * layout::WORD_BYTES,
        "planned quotient stack/scratch region must cover the validated VM operand stack"
    );
    assert_eq!(
        plan.quotient.program.eval_numer_mptr,
        plan.quotient.state_slots.eval_numer_mptr
    );
    assert_eq!(
        plan.quotient.sorted_simple.len(),
        plan.meta.num_simple_selectors
    );

    let verifier = inputs.generate_verifier_from_plan(&plan, false, false, false, false, None);
    assert_eq!(verifier.codegen_layout.proof, plan.proof_layout);
    assert_eq!(verifier.memory.vk_mptr, plan.vk_mptr);
    assert_eq!(verifier.proof_len, plan.proof_layout.proof_len);
    assert_eq!(verifier.simple_selector_cols, plan.quotient.sorted_simple);
}

#[test]
fn structured_selector_runs_do_not_group_trace_identities() {
    let lowering_source = lowering_source_corpus();
    assert!(
        !lowering_source.contains("selector_run_quotient_block")
            && !lowering_source.contains("flush_structured_selector_run"),
        "selector-run grouping should stay removed from the fixed compact default"
    );
    assert!(
        lowering_source.contains("fn push_quotient_trace(")
            && lowering_source.contains("trace_u256(mload({:#x}), {value})")
            && lowering_source.contains("mstore({:#x}, add(mload({:#x}), 1))"),
        "trace builds must still emit one trace event per emitted identity"
    );
}

#[test]
fn compact_quotient_default_matches_gas_capped_setting() {
    assert_eq!(DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES, 4);
    assert_eq!(DEFAULT_QUOTIENT_NATIVE_GATES, 4);
    let limb_vm_ops = DEFAULT_QUOTIENT_LIMB_VM_OPS;
    assert!(limb_vm_ops);

    let docs = include_str!("../../docs/reference/QUOTIENT_NUMERATOR_EVALUATOR.md");
    assert!(
        docs.contains("direct inline identities: 4"),
        "quotient evaluator docs should record the gas-capped compact default"
    );
    assert!(
        docs.contains("structured trash suffix: on"),
        "quotient evaluator docs should record the gas-capped structured-tail default"
    );
    assert!(
        docs.contains("limb VM ops: on"),
        "quotient evaluator docs should record the limb-op default"
    );
    assert!(
        docs.contains("VM CSE: off"),
        "quotient evaluator docs should record that temp-backed VM CSE is disabled"
    );
}

#[test]
fn quotient_forward_y_batch_matches_rust_reverse_fold() {
    let y = Fq::from(17u64);
    let evals = [
        Fq::from(3u64),
        Fq::from(5u64),
        Fq::from(7u64),
        Fq::from(11u64),
        Fq::from(13u64),
    ];

    let solidity_forward = evals.iter().fold(Fq::ZERO, |acc, eval| acc * y + eval);

    let mut rust_reverse = Fq::ZERO;
    let mut y_pow = Fq::ONE;
    for eval in evals.iter().rev() {
        rust_reverse += *eval * y_pow;
        y_pow *= y;
    }

    assert_eq!(solidity_forward, rust_reverse);
}

#[test]
fn quotient_selector_gap_fold_matches_rust_reverse_fold() {
    let y = Fq::from(19u64);
    let evals = [
        Fq::from(2u64),
        Fq::from(0u64),
        Fq::from(23u64),
        Fq::from(29u64),
    ];
    let selector_positions = [true, false, true, true];

    let mut y_powers = vec![Fq::ONE; evals.len()];
    for idx in 1..y_powers.len() {
        y_powers[idx] = y_powers[idx - 1] * y;
    }

    let mut previous = None;
    let mut selector_acc = Fq::ZERO;
    for (idx, (eval, selected)) in evals.iter().zip(selector_positions).enumerate() {
        if selected {
            let gap = previous.map_or(0, |prev| idx - prev);
            selector_acc *= y_powers[gap];
            selector_acc += *eval;
            previous = Some(idx);
        }
    }
    let tail = evals.len() - 1 - previous.expect("selector identity present");
    let solidity_selector_acc = selector_acc * y_powers[tail];

    let mut rust_selector_acc = Fq::ZERO;
    let mut y_pow = Fq::ONE;
    for (eval, selected) in evals.iter().zip(selector_positions).rev() {
        if selected {
            rust_selector_acc += *eval * y_pow;
        }
        y_pow *= y;
    }

    assert_eq!(solidity_selector_acc, rust_selector_acc);
}

#[test]
fn quotient_program_artifacts_match_typed_identity_stream() {
    let y = Fq::from(23u64);
    let mut values = HashMap::new();
    for (ptr, value) in [
        (0x100, 3),
        (0x120, 5),
        (0x140, 7),
        (0x160, 11),
        (0x180, 13),
        (0x1a0, 17),
        (0x1c0, 19),
    ] {
        values.insert(ptr, Fq::from(value));
    }

    let mem = |ptr| QuotientExpr::Mem(QuotientMem::Literal(ptr));
    let identities = vec![
        test_quotient_identity_with_expr(
            0,
            QuotientTarget::Main,
            quotient_add_expr(mem(0x100), mem(0x120)),
        ),
        test_quotient_identity_with_expr(
            1,
            QuotientTarget::Selector(0),
            quotient_mul_expr(mem(0x140), mem(0x160)),
        ),
        test_quotient_identity_with_expr(2, QuotientTarget::Selector(1), {
            QuotientExpr::Neg(Box::new(mem(0x180)))
        }),
        test_quotient_identity_with_expr(
            3,
            QuotientTarget::Main,
            quotient_mul_expr(quotient_add_expr(mem(0x100), mem(0x120)), mem(0x1a0)),
        ),
        test_quotient_identity_with_expr(
            4,
            QuotientTarget::Selector(0),
            quotient_add_expr(mem(0x1c0), QuotientExpr::Const(U256::from(29u64))),
        ),
    ];

    let selector_fold = VerifierBuildInputs::selector_fold_plan(&identities, 2);
    assert_eq!(
        selector_fold.gaps_by_identity,
        vec![None, Some(0), Some(0), None, Some(3)]
    );
    assert_eq!(selector_fold.tail_exponents, vec![0, 2]);

    let mut builder = QuotientProgramBuilder::default();
    for identity in &identities {
        builder.identity_expr(
            &identity.expr,
            identity.target,
            selector_fold.gap_for(identity),
        );
    }
    validate_quotient_program(&builder.bytes).expect("synthetic quotient program should validate");

    let expected = expected_linearization_artifacts_for_test(&identities, &values, y, 2);
    let actual = eval_quotient_program_artifacts_for_test(
        &builder.bytes,
        &builder.consts,
        &values,
        y,
        &selector_fold.tail_exponents,
    );

    assert_eq!(actual, expected);
}

#[test]
fn quotient_execution_manifest_expands_native_callback_ranges() {
    let inline = test_quotient_identity_with_expr(
        0,
        QuotientTarget::Main,
        QuotientExpr::Const(U256::from(3u64)),
    );
    let native_gate = test_quotient_identity_with_expr(
        1,
        QuotientTarget::Selector(0),
        QuotientExpr::Const(U256::from(5u64)),
    );
    let interpreted_gate = test_quotient_identity_with_expr(
        2,
        QuotientTarget::Main,
        QuotientExpr::Const(U256::from(7u64)),
    );
    let permutation_0 = test_quotient_identity(
        3,
        QuotientIdentitySource::Permutation { identity_index: 0 },
        QuotientTarget::Main,
    );
    let permutation_1 = test_quotient_identity(
        4,
        QuotientIdentitySource::Permutation { identity_index: 1 },
        QuotientTarget::Main,
    );
    let lookup = test_quotient_identity(
        5,
        QuotientIdentitySource::Lookup {
            identity_index: 0,
            lookup_index: 0,
            lookup_name: "lookup_0".to_string(),
        },
        QuotientTarget::Main,
    );
    let trash = test_quotient_identity(
        6,
        QuotientIdentitySource::Trash {
            trash_index: 0,
            trash_name: "trash_0".to_string(),
        },
        QuotientTarget::Main,
    );
    let expected = vec![
        inline.clone(),
        native_gate.clone(),
        interpreted_gate.clone(),
        permutation_0.clone(),
        permutation_1.clone(),
        lookup.clone(),
        trash.clone(),
    ];
    let plan = test_quotient_execution_plan(
        expected.clone(),
        vec![inline],
        vec![
            QuotientProgramItem::NativeIdentity(0),
            QuotientProgramItem::Identity(interpreted_gate),
            QuotientProgramItem::NativePermutation,
            QuotientProgramItem::NativeLookup,
        ],
        vec![native_gate],
        vec![permutation_0, permutation_1],
        vec![lookup],
        vec![trash],
    );

    plan.validate_execution_manifest(&expected)
        .expect("mixed execution plan should preserve identity stream");
    let executions = plan
        .execution_manifest()
        .expect("manifest should reconstruct")
        .into_iter()
        .map(|entry| entry.execution)
        .collect::<Vec<_>>();

    assert_eq!(
        executions,
        vec![
            QuotientExecutionKind::Inline,
            QuotientExecutionKind::NativeIdentity { native_index: 0 },
            QuotientExecutionKind::Interpreted,
            QuotientExecutionKind::NativePermutation,
            QuotientExecutionKind::NativePermutation,
            QuotientExecutionKind::NativeLookup,
            QuotientExecutionKind::StructuredTail,
        ]
    );
}

#[test]
fn quotient_execution_manifest_rejects_reordered_native_range() {
    let inline = test_quotient_identity_with_expr(
        0,
        QuotientTarget::Main,
        QuotientExpr::Const(U256::from(3u64)),
    );
    let permutation_0 = test_quotient_identity(
        1,
        QuotientIdentitySource::Permutation { identity_index: 0 },
        QuotientTarget::Main,
    );
    let permutation_1 = test_quotient_identity(
        2,
        QuotientIdentitySource::Permutation { identity_index: 1 },
        QuotientTarget::Main,
    );
    let expected = vec![inline.clone(), permutation_0.clone(), permutation_1.clone()];
    let mut plan = test_quotient_execution_plan(
        expected.clone(),
        vec![inline],
        vec![QuotientProgramItem::NativePermutation],
        Vec::new(),
        vec![permutation_0, permutation_1],
        Vec::new(),
        Vec::new(),
    );
    plan.native_permutation_identities.swap(0, 1);

    let err = plan
        .validate_execution_manifest(&expected)
        .expect_err("reordered native range must not validate");
    assert!(
        err.contains("mismatch at position"),
        "unexpected manifest error: {err}"
    );
}

#[test]
fn quotient_execution_manifest_rejects_bad_native_identity_index() {
    let native_gate = test_quotient_identity_with_expr(
        0,
        QuotientTarget::Main,
        QuotientExpr::Const(U256::from(5u64)),
    );
    let plan = test_quotient_execution_plan(
        vec![native_gate.clone()],
        Vec::new(),
        vec![QuotientProgramItem::NativeIdentity(1)],
        vec![native_gate],
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );

    let err = plan
        .execution_manifest()
        .expect_err("out-of-range native callback body must fail");
    assert!(
        err.contains("has no callback body"),
        "unexpected native identity error: {err}"
    );
}

#[test]
fn quotient_program_items_emit_bytecode_markers_in_manifest_order() {
    let interpreted = test_quotient_identity_with_expr(
        0,
        QuotientTarget::Selector(0),
        QuotientExpr::Const(U256::from(11u64)),
    );
    let selector_fold =
        VerifierBuildInputs::selector_fold_plan(std::slice::from_ref(&interpreted), 1);
    let mut builder = QuotientProgramBuilder::default();

    builder.native_identity(7);
    builder.identity_expr(
        &interpreted.expr,
        interpreted.target,
        selector_fold.gap_for(&interpreted),
    );
    builder.native_permutation();
    builder.native_lookup();

    validate_quotient_program(&builder.bytes)
        .expect("native markers and interpreted fold should validate");
    assert_eq!(
        quotient_bytecode_events_for_test(&builder.bytes),
        vec![
            TestQuotientBytecodeEvent::NativeIdentity(7),
            TestQuotientBytecodeEvent::Fold(QuotientTarget::Selector(0)),
            TestQuotientBytecodeEvent::NativePermutation,
            TestQuotientBytecodeEvent::NativeLookup,
        ]
    );
}

#[test]
fn selector_sparse_fold_exhaustive_matches_naive_global_y_powers() {
    let y = Fq::from(31u64);
    for len in 1..=8usize {
        let cases = 3usize.pow(len as u32);
        for mut case in 0..cases {
            let mut identities = Vec::with_capacity(len);
            for idx in 0..len {
                let digit = case % 3;
                case /= 3;
                let target = match digit {
                    0 => QuotientTarget::Main,
                    1 => QuotientTarget::Selector(0),
                    _ => QuotientTarget::Selector(1),
                };
                identities.push(test_quotient_identity_with_expr(
                    idx,
                    target,
                    QuotientExpr::Const(U256::from((idx as u64 + 2) * 17)),
                ));
            }

            let selector_fold = VerifierBuildInputs::selector_fold_plan(&identities, 2);
            let values = HashMap::new();
            let expected = expected_linearization_artifacts_for_test(&identities, &values, y, 2);

            let mut sparse_main = Fq::ZERO;
            let mut sparse_selectors = vec![Fq::ZERO; 2];
            for identity in &identities {
                let value = eval_quotient_expr_for_test(&identity.expr, &values);
                match identity.target {
                    QuotientTarget::Main => {
                        sparse_main = sparse_main * y + value;
                    }
                    QuotientTarget::Selector(selector_idx) => {
                        sparse_main *= y;
                        let gap =
                            selector_fold.gap_for(identity).expect("selector identity has gap");
                        sparse_selectors[selector_idx] =
                            sparse_selectors[selector_idx] * fq_pow(y, gap) + value;
                    }
                }
            }
            for (bucket, tail) in
                sparse_selectors.iter_mut().zip(selector_fold.tail_exponents.iter())
            {
                *bucket *= fq_pow(y, *tail);
            }

            assert_eq!(sparse_main, expected.main_numerator);
            assert_eq!(sparse_selectors, expected.selector_buckets);
            assert_eq!(-sparse_main, expected.quotient_expected_eval);
        }
    }
}

#[test]
fn quotient_identity_manifest_preserves_order_and_metadata() {
    let gate_source = QuotientIdentitySource::Gate {
        gate_index: 2,
        gate_name: "custom_gate".to_string(),
        constraint_index: 1,
        constraint_name: "constraint_b".to_string(),
        polynomial_index: 1,
    };
    let parts = QuotientIdentityParts {
        gates: vec![test_quotient_identity(
            0,
            gate_source.clone(),
            QuotientTarget::Selector(0),
        )],
        permutation: vec![test_quotient_identity(
            1,
            QuotientIdentitySource::Permutation { identity_index: 0 },
            QuotientTarget::Main,
        )],
        lookup: vec![test_quotient_identity(
            2,
            QuotientIdentitySource::Lookup {
                identity_index: 0,
                lookup_index: 0,
                lookup_name: "lookup_0".to_string(),
            },
            QuotientTarget::Main,
        )],
        trash: vec![test_quotient_identity(
            3,
            QuotientIdentitySource::Trash {
                trash_index: 0,
                trash_name: "partial_round_gate".to_string(),
            },
            QuotientTarget::Main,
        )],
        sorted_simple: vec![42],
    };

    let manifest = parts.manifest();

    assert_eq!(manifest.gate_identities, 1);
    assert_eq!(manifest.permutation_identities, 1);
    assert_eq!(manifest.lookup_identities, 1);
    assert_eq!(manifest.trash_identities, 1);
    assert_eq!(
        manifest.entries.iter().map(|entry| entry.global_index).collect::<Vec<_>>(),
        vec![0, 1, 2, 3]
    );
    assert_eq!(manifest.entries[0].source, gate_source);
    assert_eq!(
        manifest.entries[0].target,
        QuotientIdentityManifestTarget::Selector {
            selector_index: 0,
            fixed_column: 42,
        }
    );
    assert!(matches!(
        manifest.entries[3].source,
        QuotientIdentitySource::Trash { ref trash_name, .. } if trash_name == "partial_round_gate"
    ));
}

#[test]
fn limb7_linear_chain_is_recognized_as_native_helper_call() {
    let lines = [
        "let c0 := 0x100000000000000",
        "let m0 := mulmod(c0, x1, r)",
        "let a0 := addmod(x0, m0, r)",
        "let m1 := mulmod(0x10000000000000000000000000000, x2, r)",
        "let a1 := addmod(a0, m1, r)",
        "let m2 := mulmod(0x400000000, x3, r)",
        "let a2 := addmod(a1, m2, r)",
        "let m3 := mulmod(0x40000000000000000000000, x4, r)",
        "let a3 := addmod(a2, m3, r)",
        "let m4 := mulmod(0x1000, x5, r)",
        "let a4 := addmod(a3, m4, r)",
        "let m5 := mulmod(0x100000000000000000, x6, r)",
        "let a5 := addmod(a4, m5, r)",
    ]
    .iter()
    .map(|line| line.to_string())
    .collect::<Vec<_>>();

    let specialized = VerifierBuildInputs::specialize_limb7_chains(&lines);

    assert_eq!(
        specialized,
        vec![
            "let c0 := 0x100000000000000".to_string(),
            "let a5 := q_limb7(x0, x1, x2, x3, x4, x5, x6)".to_string(),
        ]
    );
}

#[test]
fn transcript_memory_bound_handles_wide_bls_advice_phase() {
    let mut cs = ConstraintSystem::default();
    let mut advices = Vec::new();
    for _ in 0..64 {
        advices.push(cs.advice_column());
    }
    cs.create_gate("open wide advice phase", |meta| {
        let acc = advices.iter().fold(Expression::Constant(Fq::ZERO), |acc, col| {
            acc + meta.query_advice(*col, Rotation::cur())
        });
        Constraints::without_selector(vec![("open wide advice phase", acc)])
    });
    let meta = ConstraintSystemMeta::new(&cs, 0);

    let words = VerifierBuildInputs::transcript_buffer_words_bound(&meta, 0);

    // Regression for the BN254-era `n * 2 + 1` sizing bug: the BLS
    // transcript absorbs each proof commitment as a 128-byte
    // EIP-2537-padded G1, so 64 first-phase advice commitments need
    // vk_digest + committed_pi + num_instances + 64 G1s + squeeze seed.
    let first_phase_run = 32 + 128 + 32 + 64 * 128 + 32;
    assert!(words * 0x20 >= first_phase_run);
    assert!(
        words > 64 * 2 + 1,
        "transcript memory bound must not regress to the BN254 stride"
    );
}

#[test]
fn eip2537_calls_forward_remaining_gas() {
    let verifier_template = verifier_template_corpus();
    let pcs_codegen = include_str!("kzg/mod.rs");

    assert!(
        verifier_template
            .contains("staticcall(gas(), {{ template_constants.eip2537.g1add_address|hex() }}")
            && verifier_template
                .contains("staticcall(gas(), {{ template_constants.eip2537.g1msm_address|hex() }}")
            && verifier_template.contains(
                "staticcall(gas(), {{ template_constants.eip2537.pairing_address|hex() }}"
            ),
        "main verifier template should forward remaining gas to EIP-2537 precompiles"
    );
    assert!(
        pcs_codegen.contains("staticcall(gas(), 0x0c")
            && pcs_codegen.contains("staticcall(gas(), 0x0b"),
        "PCS emitter should forward remaining gas to EIP-2537 precompiles"
    );
    for source in [verifier_template, pcs_codegen] {
        assert!(
            !source.contains("g1msm_gas_cap")
                && !source.contains("G1ADD_GAS_CAP")
                && !source.contains("PAIRING_SMOKE_GAS_CAP")
                && !source.contains("final_pairing_gas_cap"),
            "EIP-2537 gas-cap literals must not be rendered or computed"
        );
    }
}

#[test]
fn failed_success_paths_do_not_enter_ec_precompiles() {
    let verifier_template = verifier_template_corpus();
    let pcs_codegen = include_str!("kzg/mod.rs");

    assert!(
            verifier_template.contains("if iszero(success) { revert(0, 0) }\n            }\n\n            {%- if self.expected_has_accumulator %}\n            // Fail malformed accumulator public inputs before transcript"),
            "ABI/proof length/instance shape checks should fail before accumulator or transcript parsing"
        );
    assert!(
            verifier_template.contains("success := validate_public_accumulator(success, r)\n            if iszero(success) { revert(0, 0) }\n            {%- endif %}\n\n            {%- if self.gas_checkpoints %}\n            gas_checkpoint(2)"),
            "accumulator precheck should fail before transcript parsing"
        );
    assert!(
        verifier_template.contains(
            "success := and(success, lt(inst_be, r))\n                    // Instances are passed BE in calldata, matching the\n                    // Keccak Fq transcript input.\n                    buf_len := common_word(buf_len, inst_be)\n                }\n                if iszero(success) { revert(0, 0) }"
        ),
        "non-canonical public instances should fail before proof transcript parsing"
    );
    assert!(
        verifier_template.contains(
            "if iszero(success) { revert(0, 0) }\n\n            {%- match quotient_external %}"
        ),
        "failed Lagrange/common-polynomial setup should fail before quotient reconstruction"
    );
    for source in [verifier_template, pcs_codegen] {
        assert!(
                !source.contains("and(success, staticcall"),
                "Yul does not short-circuit and(success, staticcall(...)); guard precompile calls with if success"
            );
        assert!(
                !source.contains("and(\n                            success,\n                            staticcall"),
                "multi-line and(success, staticcall(...)) must not reappear"
            );
    }
    assert!(
            verifier_template.contains(
                "if iszero(success) { revert(0, 0) }\n            success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)"
            ),
            "final pairing block should revert before staging/calling the pairing precompile when success is already false"
        );
    assert!(
        pcs_codegen.contains("if success {")
            && pcs_codegen.contains("success := staticcall(gas(), 0x0c")
            && pcs_codegen.contains("success := staticcall(gas(), 0x0b"),
        "PCS emitter should guard final MSM/add precompile calls with if success"
    );
}

#[test]
fn verifier_constructor_smoke_tests_runtime_prerequisites() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains("function require_eip2537_precompiles() private view"),
        "generated verifier should include a deployment-time runtime prerequisite smoke test"
    );
    for required in [
        "Smoke-check the Cancun/EIP-2537 runtime features",
        "mcopy(add(scratch, {{ template_constants.word_bytes|hex() }}), scratch, {{ template_constants.word_bytes|hex() }})",
        "eq(mload(add(scratch, {{ template_constants.word_bytes|hex() }})), 0x1234)",
        "non-Cancun fork fails during deployment",
        "G1ADD(identity, identity) -> identity",
        "Worst-case generated G1MSM with all identity/zero terms",
        "constructor_g1msm_smoke_input_bytes",
        "PAIRING_CHECK([(identity_g1, identity_g2), (identity_g1, identity_g2)])",
        "staticcall(gas(), {{ template_constants.eip2537.g1add_address|hex() }}",
        "staticcall(gas(), {{ template_constants.eip2537.g1msm_address|hex() }}",
        "staticcall(gas(), {{ template_constants.eip2537.pairing_address|hex() }}",
        "template_constants.eip2537.g1add_address",
        "template_constants.eip2537.g1msm_address",
        "template_constants.eip2537.pairing_address",
        "eq(returndatasize(), {{ template_constants.g1_bytes|hex() }})",
        "eq(returndatasize(), {{ template_constants.word_bytes|hex() }})",
    ] {
        assert!(
            verifier_template.contains(required),
            "constructor runtime-prerequisite smoke test missing expected check: {required}"
        );
    }
    assert_eq!(
        verifier_template.matches("require_eip2537_precompiles();").count(),
        4,
        "every generated constructor shape should run the runtime-prerequisite smoke test"
    );
    assert!(
        verifier_template.contains("support MCOPY and EIP-2537"),
        "generated source should state the target-chain opcode/precompile requirement"
    );
}

#[test]
fn external_quotient_template_has_no_unpinned_fallback() {
    let verifier_template = verifier_template_corpus();

    assert!(
        !verifier_template.contains("AUTHORIZED_QUOTIENT_CODEHASH"),
        "external quotient builds must use generated expected length/hash constants"
    );
    assert!(
        !verifier_template.contains("authorizedQuotient.code.length != 0"),
        "constructor must not pin whichever quotient address the deployer passed"
    );
}

#[test]
fn pinned_dependencies_are_rechecked_during_verification() {
    let verifier_template = verifier_template_corpus();

    for required in [
        "EXPECTED_VK_PAYLOAD_LENGTH",
        "eq(extcodesize(vk), EXPECTED_VK_LENGTH)",
        "eq(extcodehash(vk), EXPECTED_VK_CODEHASH_WORD)",
        "extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)",
        "eq(extcodesize(quotientEvaluator), EXPECTED_QUOTIENT_LENGTH)",
        "eq(extcodehash(quotientEvaluator), EXPECTED_QUOTIENT_CODEHASH_WORD)",
        "Re-check the pinned VK dependency on every proof",
        "Re-check the pinned runtime before every",
    ] {
        assert!(
            verifier_template.contains(required),
            "template should re-check pinned dependency at verification time: {required}"
        );
    }
}

#[test]
fn separate_vk_runtime_is_prefixed_with_invalid_opcode() {
    let verifier_template = verifier_template_corpus();
    let vk_template = include_str!("../../templates/contracts/Halo2VerifyingKey.sol");

    assert!(
        vk_template.contains("mstore8(runtime, 0xfe)"),
        "VK runtime must start with an unconditional INVALID opcode"
    );
    assert!(
        vk_template.contains("return(runtime,"),
        "VK constructor must return the prefixed runtime, not just the payload"
    );
    assert!(
        verifier_template.contains("EXPECTED_VK_LENGTH = {{ vk_len + 1 }}"),
        "verifier must pin the full INVALID-prefixed VK runtime length"
    );
    assert!(
        verifier_template.contains("extcodecopy(vk, VK_MPTR, 0x01, EXPECTED_VK_PAYLOAD_LENGTH)"),
        "verifier must skip the INVALID prefix while loading the VK payload"
    );
}

#[test]
fn accumulator_schema_is_checked_against_instance_count() {
    let verifier_template = verifier_template_corpus();
    let spec = include_str!("../../docs/reference/HALO2_MIDNIGHT_VERIFIER_SPEC.md");

    assert!(
        verifier_template.contains("eq({{ num_instances }}, calldataload(NUM_INSTANCE_CPTR))"),
        "verifier must check calldata instance length against the generated public-input width"
    );
    assert!(
        verifier_template.contains("add(INSTANCE_CPTR, {{ (num_instances * 32)|hex() }})"),
        "verifier must reject extra trailing calldata after the generated instance vector"
    );
    assert!(
            verifier_template.contains("RHS layout for this generated verifier is fully collapsed"),
            "no-tail accumulator renders must explicitly document that no fixed-base scalar tail exists"
        );
    assert!(
        verifier_template.contains("collapsed point pair"),
        "point-pair accumulator renders must explicitly document implicit scalar semantics"
    );
    assert!(
        verifier_template.contains("RHS layout for this generated verifier is partially"),
        "tail accumulator renders must explicitly document fixed-base scalar tail semantics"
    );
    assert!(
        verifier_template.contains("{%- if acc_fixed_bases.len() > 0 %}"),
        "fixed-base scalar tail parsing should only render when generated bases exist"
    );
    for required in [
        "GeneratorConfig::new",
        "with_accumulator",
        "The accumulator is not passed through a separate ABI argument",
        "checked tail convention",
    ] {
        assert!(
            spec.contains(required),
            "accumulator activation/layout docs should mention: {required}"
        );
    }
}

#[test]
fn vk_header_is_cross_checked_against_generated_constants() {
    let verifier_template = verifier_template_corpus();

    for expected_check in [
        "eq(mload(NUM_INSTANCES_MPTR), {{ num_instances }})",
        "eq(mload(K_MPTR), {{ k }})",
        "eq(mload(HAS_ACCUMULATOR_MPTR), {{ expected_has_accumulator_word }})",
        "eq(mload(ACC_OFFSET_MPTR), {{ expected_acc_offset }})",
        "eq(mload(NUM_ACC_LIMBS_MPTR), {{ expected_num_acc_limbs }})",
        "eq(mload(NUM_ACC_LIMB_BITS_MPTR), {{ expected_num_acc_limb_bits }})",
    ] {
        assert!(
            verifier_template.contains(expected_check),
            "pinned verifier should cross-check generated VK header value: {expected_check}"
        );
    }
    assert!(
        verifier_template.contains("Cross-check loaded VK header words")
            && verifier_template.contains("generator drift before calldata parsing"),
        "template should document the VK header generator-safety boundary"
    );
    assert!(
        verifier_template.contains("{%- if self.expected_has_accumulator %}")
            && verifier_template.contains("let bits := {{ self.expected_num_acc_limb_bits }}")
            && verifier_template.contains("let n := {{ self.expected_num_acc_limbs }}"),
        "accumulator decoding should be rendered only for generated accumulator VKs"
    );
}

#[test]
fn accumulator_limb_packing_is_checked_before_decoding() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains("function check_acc_coord_packing"),
        "accumulator decoder must reject unused high bits in packed limb words"
    );
    assert!(
        verifier_template.contains("ok := check_acc_coord_packing(src, bits, n, limbs_per_word)"),
        "accumulator coordinate decoding must apply packing canonicality before masking limbs"
    );
}

#[test]
fn accumulator_points_are_prevalidated_before_transcript_work() {
    let verifier_template = verifier_template_corpus();

    for required in [
        "function validate_public_accumulator(success, r) -> out",
        "Fail malformed accumulator public inputs before transcript",
        "success := validate_public_accumulator(success, r)",
        "gas_checkpoint(2) // after VK loading + accumulator public-input precheck",
        "Batch the prevalidated public IVC accumulator pairing equation",
    ] {
        assert!(
                verifier_template.contains(required),
                "accumulator validation should be split into early precheck and late pairing batch: {required}"
            );
    }
}

#[test]
fn accumulator_scalars_are_range_checked_where_they_are_read() {
    let verifier_template = verifier_template_corpus();

    // `validate_public_accumulator` runs before the transcript instance loop
    // that rejects non-canonical instance words, and EIP-2537 G1MSM reduces
    // scalars mod r implicitly. Canonicality must therefore be enforced at the
    // read sites in this helper rather than inherited from a later template.
    for required in [
        "out := and(out, lt(lhs_scalar, r))",
        "out := and(out, lt(rhs_scalar, r))",
        "out := and(out, lt(fixed_scalar_{{ loop.index0 }}, r))",
    ] {
        assert!(
            verifier_template.contains(required),
            "accumulator scalars must be range-checked against r where they are read: {required}"
        );
    }
}

#[test]
fn accumulator_decoder_rejects_noncanonical_infinity() {
    let verifier_template = verifier_template_corpus();

    for required in [
        "EIP-2537 reserves affine (0,0) for the point",
        "let decoded_zero := iszero(or(or(x_hi, x_lo), or(y_hi, y_lo)))",
        "ok := and(ok, iszero(decoded_zero))",
        "is_acc_encoded_identity(src)",
    ] {
        assert!(
            verifier_template.contains(required),
            "accumulator decoder should reject non-canonical infinity encodings: {required}"
        );
    }
}

#[test]
fn accumulator_encoding_validation_rejects_dead_configs() {
    let fully_collapsed = AccumulatorEncoding::new(4, 7, 56);
    assert_eq!(
        fully_collapsed.fully_collapsed_public_input_words(),
        Ok(AccumulatorEncoding::FULLY_COLLAPSED_PUBLIC_INPUT_WORDS)
    );
    assert!(fully_collapsed.validate_for_num_instances(14).is_ok());
    assert_eq!(fully_collapsed.fixed_scalar_count(14), Ok(0));
    assert_eq!(fully_collapsed.fixed_scalar_count(17), Ok(3));

    let point_pair = AccumulatorEncoding::point_pair(4, 7, 56);
    assert_eq!(
        point_pair.fully_collapsed_public_input_words(),
        Ok(AccumulatorEncoding::POINT_PAIR_PUBLIC_INPUT_WORDS)
    );
    assert!(point_pair.validate_for_num_instances(12).is_ok());
    assert_eq!(point_pair.fixed_scalar_count(12), Ok(0));
    assert!(matches!(
        point_pair.fixed_scalar_count(13),
        Err(GeneratorError::UnsupportedAccumulatorEncoding {
            reason: "point-pair accumulator encoding does not support a fixed-base scalar tail",
            ..
        })
    ));

    let wrong_limb_shape = AccumulatorEncoding::new(4, 8, 32);
    assert!(matches!(
        wrong_limb_shape.validate_for_num_instances(14),
        Err(GeneratorError::UnsupportedAccumulatorEncoding {
            num_limbs: 8,
            num_limb_bits: 32,
            ..
        })
    ));

    let out_of_bounds = AccumulatorEncoding::new(5, 7, 56);
    assert!(matches!(
        out_of_bounds.validate_for_num_instances(14),
        Err(GeneratorError::UnsupportedAccumulatorEncoding {
            offset: 5,
            reason: "accumulator public-input tail exceeds num_instances",
            ..
        })
    ));
}

#[test]
fn generated_solidity_pragmas_require_mcopy_capable_compiler() {
    for (name, source) in [
        ("Halo2Verifier.sol", verifier_template_corpus()),
        (
            "Halo2VerifyingKey.sol",
            include_str!("../../templates/contracts/Halo2VerifyingKey.sol"),
        ),
        (
            "Halo2QuotientEvaluator.sol",
            include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol"),
        ),
    ] {
        assert!(
            source.contains("pragma solidity ^0.8.24;"),
            "{name} must require Solidity 0.8.24+ for Cancun Yul opcodes"
        );
    }
}

#[test]
fn verifier_checks_canonical_dynamic_abi_heads() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains(
            "eq(calldataload({{ abi_selector_bytes|hex() }}), {{ abi_proof_head_offset|hex() }})"
        ),
        "verifier must read the proof dynamic ABI head"
    );
    assert!(
            verifier_template.contains(
                "eq(calldataload({{ abi_instances_head_cptr|hex() }}), sub(NUM_INSTANCE_CPTR, {{ abi_selector_bytes|hex() }}))"
            ),
            "verifier must read the instances dynamic ABI head"
        );
}

#[test]
fn generated_comments_describe_padded_g1_calldata() {
    let verifier_template = verifier_template_corpus();

    for stale in [
        "zcash-compressed form",
        "decompressed inline",
        "Helpers: modexp, decompress",
        "Each compressed G1 absorbed",
        "Per-category bases for decompressed G1 commitments",
    ] {
        assert!(
                !verifier_template.contains(stale),
                "generated verifier comments must not describe the old compressed-G1 calldata path: {stale}"
            );
    }

    assert!(
        verifier_template.contains("proof shim repacks midnight-proofs' native compressed stream"),
        "generated verifier comments should document the off-chain repacking boundary"
    );
    assert!(
        verifier_template.contains("validates and absorbs that 128-byte form"),
        "generated verifier comments should describe the current EIP-2537-padded G1 path"
    );
}

#[test]
fn point_validation_boundary_is_documented_and_plan_checked() {
    let verifier_template = verifier_template_corpus();
    let protocol_source = include_str!("protocol/mod.rs");
    let test_source = include_str!("../test.rs");

    assert!(
        verifier_template.contains("This helper does not run an independent curve/subgroup"),
        "common_uncompressed_g1 should document that curve/subgroup checks are delegated"
    );
    assert!(
        verifier_template.contains("consumed by an EIP-2537 G1MSM or pairing path"),
        "generated comments should name the subgroup-checking precompile paths"
    );
    assert!(
        protocol_source.contains("Every proof G1 commitment absorbed into Fiat-Shamir"),
        "ProtocolPlan validation should document absorbed-point PCS/precompile coverage"
    );
    assert!(
        protocol_source.contains("absorbed but never opened by PCS"),
        "ProtocolPlan validation should reject absorbed unopened advice commitments"
    );
    for required_test in [
        "every_proof_g1_rejects_noncanonical_coordinates",
        "every_proof_g1_rejects_off_curve_coordinates",
    ] {
        assert!(
            test_source.contains(required_test),
            "negative proof-G1 mutation coverage should include {required_test}"
        );
    }
}

#[test]
fn trace_u256_uses_planned_memory_slot() {
    let verifier_template = verifier_template_corpus();
    let quotient_template = include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol");
    let memory_source = include_str!("layout/memory.rs");

    for source in [verifier_template, quotient_template] {
        assert!(
            source.contains("TRACE_U256_MPTR"),
            "trace_u256 should write through a planned memory slot"
        );
        assert!(
            !source.contains("0x5e00"),
            "trace_u256 must not use the old hard-coded scratch word"
        );
    }
    assert!(
        memory_source.contains("trace_u256_log_word"),
        "memory planner should register the trace_u256 log buffer"
    );
}

#[test]
fn differential_trace_hooks_cover_expected_categories() {
    let verifier_template = verifier_template_corpus();
    let pcs_source = include_str!("kzg/mod.rs");

    for (name, needle) in [
        (
            "user transcript challenges",
            "1000 + phase.challenge_offset + j",
        ),
        ("quotient numerator", "trace_u256(36,"),
        ("f_eval", "trace_u256(31,"),
        ("final MSM commitment", "trace_point(33,"),
        ("pairing lhs input", "trace_point(27,"),
        ("pairing rhs input", "trace_point(28,"),
        ("final result", "trace_u256(35,"),
        ("selector folds", "selector_trace_base + loop.index0"),
    ] {
        assert!(
            verifier_template.contains(needle),
            "verifier template missing {name} trace hook"
        );
    }

    for (name, needle) in [
        (
            "serialized PCS point sets",
            "trace::PCS_SERIALIZED_POINT_SET_BASE + set_idx as u64",
        ),
        (
            "PCS q_com commitments",
            "trace::PCS_Q_COM_BASE + set_idx as u64",
        ),
    ] {
        assert!(
            pcs_source.contains(needle),
            "PCS emitter missing {name} trace hook"
        );
    }
}

#[test]
fn quotient_vm_opcode_and_token_tables_match_template_cases() {
    let quotient_template =
        include_str!("../../templates/partials/quotient_numerator/QuotientNumeratorBlock.yul");

    for spec in QUOTIENT_VM_SPEC.opcodes {
        let name = spec.name;
        let needle = [
            "case {{ template_constants.quotient_vm.op.",
            name,
            "|hex() }}",
        ]
        .concat();
        assert!(
            quotient_template.contains(&needle),
            "quotient VM template missing opcode {name} template constant"
        );
    }
    assert!(
        !quotient_template.contains("case 0x1a"),
        "stale native-trash opcode must not remain in quotient VM template"
    );

    for spec in QUOTIENT_VM_SPEC.mem_tokens {
        let name = spec.name;
        let field = match name {
            "L_0_MPTR" => "l0",
            "L_LAST_MPTR" => "l_last",
            "L_BLIND_MPTR" => "l_blind",
            "BETA_MPTR" => "beta",
            "GAMMA_MPTR" => "gamma",
            "X_MPTR" => "x",
            "THETA_MPTR" => "theta",
            "TRASH_CHALLENGE_MPTR" => "trash_challenge",
            "INSTANCE_EVAL_MPTR" => "instance_eval",
            _ => panic!("unmapped quotient VM memory token {name}"),
        };
        let needle = [
            "case {{ template_constants.quotient_vm.mem.",
            field,
            "|hex() }} { q_ptr := ",
            name,
        ]
        .concat();
        assert!(
            quotient_template.contains(&needle),
            "quotient VM template missing memory token {name} template constant"
        );
    }
    assert_eq!(QUOTIENT_VM_SPEC.limb_count, layout::quotient_limb::LIMBS);
    assert_eq!(
        QUOTIENT_VM_SPEC.limb_pairwise_terms,
        layout::quotient_limb::PAIRWISE_TERMS
    );
    assert_eq!(
        QUOTIENT_VM_SPEC.limb_pairwise_coeffs,
        layout::quotient_limb::PAIRWISE_COEFFS
    );
}

#[test]
fn quotient_vm_lengths_are_derived_from_opcode_spec() {
    for spec in QUOTIENT_VM_SPEC.opcodes {
        if spec.byte_len == 0 {
            continue;
        }
        let bytes = vec![spec.opcode; spec.byte_len];
        assert_eq!(
            quotient_op_len(&bytes, 0),
            spec.byte_len,
            "opcode {} length should come from QuotientVmSpec",
            spec.name
        );
    }
}

#[test]
fn quotient_vm_safety_validator_rejects_malformed_programs() {
    let underflow =
        validate_quotient_program(&[Q_OP_ADD]).expect_err("ADD without operands must underflow");
    assert!(
        underflow.contains("stack underflow"),
        "unexpected underflow error: {underflow}"
    );

    let leak =
        validate_quotient_program(&[Q_OP_PUSH_CONST_U8, 0, Q_OP_PUSH_CONST_U8, 0, Q_OP_FOLD_MAIN])
            .expect_err("fold with leaked spilled stack value must fail");
    assert!(
        leak.contains("requires exactly 1 stack value"),
        "unexpected leak error: {leak}"
    );

    let bad_token = validate_quotient_program(&[Q_OP_PUSH_MEM_TOKEN, 0xff, Q_OP_FOLD_MAIN])
        .expect_err("unknown memory token must fail");
    assert!(
        bad_token.contains("unknown quotient VM memory token"),
        "unexpected token error: {bad_token}"
    );

    let truncated =
        validate_quotient_program(&[Q_OP_PUSH_CONST, 0]).expect_err("truncated operand must fail");
    assert!(
        truncated.contains("truncated quotient VM"),
        "unexpected truncation error: {truncated}"
    );
}

#[test]
fn quotient_vm_safety_validator_accepts_byte_programs() {
    let bytes = [Q_OP_PUSH_CONST_U8, 0, Q_OP_POW5, Q_OP_FOLD_MAIN];
    assert_eq!(validate_quotient_program(&bytes).unwrap(), 1);
}

#[test]
fn quotient_vm_runtime_asserts_exact_program_termination() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains("if iszero(eq(q_pc, q_end)) { revert(0, 0) }")
            && verifier_template.contains("if q_has_top { revert(0, 0) }"),
        "quotient VM must fail closed when bytecode over-runs q_end or leaves a live stack value"
    );
}

#[test]
fn normalized_yul_assignment_parser_tolerates_formatting_variants() {
    assert_eq!(
        yul_let_assignment("  let   z:=addmod(a, b, r)  "),
        Some(("z".to_string(), "addmod(a, b, r)".to_string()))
    );
    assert_eq!(
        yul_addmod_assignment("let z := addmod ( a, mulmod(b, c, r), r )"),
        Some((
            "z".to_string(),
            "a".to_string(),
            "mulmod(b, c, r)".to_string()
        ))
    );
    assert_eq!(
        yul_mulmod_assignment("let z:=mulmod(a,b,r)"),
        Some(("z".to_string(), "a".to_string(), "b".to_string()))
    );
}

#[test]
fn field_negations_used_by_traces_are_canonical() {
    let quotient_template =
        include_str!("../../templates/partials/quotient_numerator/QuotientNumeratorBlock.yul");
    let evaluator_source = include_str!("quotient_numerator/yul_emit.rs");
    let pcs_source = include_str!("kzg/mod.rs");

    for (name, source, needle) in [
            (
                "byte quotient VM negation",
                quotient_template,
                "q_top := addmod(0, sub(r, q_top), r)",
            ),
            (
                "structured quotient linearization expected eval",
                quotient_template,
                "let linearization_expected_eval := addmod(0, sub(r, mload({{ program.eval_numer_mptr|hex() }})), r)",
            ),
            (
                "legacy direct quotient linearization expected eval",
                quotient_template,
                "let linearization_expected_eval := addmod(0, sub(r, quotient_eval_numer), r)",
            ),
            (
                "native evaluator negation",
                evaluator_source,
                "addmod(0, sub(r, {var}), r)",
            ),
            (
                "final pairing negative v scalar",
                pcs_source,
                "addmod(0, sub(r, mload(V_MPTR)), r)",
            ),
        ] {
            assert!(
                source.contains(needle),
                "{name} should canonicalize zero negations with addmod"
            );
        }
}

#[test]
fn quotient_helper_definitions_live_in_shared_partial() {
    let verifier_template = include_str!("../../templates/contracts/Halo2Verifier.sol");
    let quotient_and_linearization =
        include_str!("../../templates/partials/verifier/QuotientAndLinearization.yul");
    let quotient_evaluator_template =
        include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol");
    let quotient_helpers =
        include_str!("../../templates/partials/quotient_numerator/QuotientHelpers.yul");

    assert!(
            quotient_and_linearization.contains(
                "{%- when None %}\n            {%- include \"partials/quotient_numerator/QuotientHelpers.yul\" %}\n            {%- include \"partials/quotient_numerator/QuotientNumeratorBlock.yul\" %}"
            ),
            "monolithic verifier quotient path should include helpers beside the numerator block"
        );
    assert!(
            quotient_evaluator_template.contains(
                "{%- include \"partials/quotient_numerator/QuotientHelpers.yul\" %}\n            {%- include \"partials/quotient_numerator/QuotientNumeratorBlock.yul\" %}"
            ),
            "external evaluator should include helpers beside the numerator block"
        );
    for helper in [
        "function q_pow5(",
        "function q_limb7(",
        "function q_limb7_wide(",
    ] {
        assert!(
            quotient_helpers.contains(helper),
            "quotient helper partial should define {helper}"
        );
        assert!(
            !verifier_template.contains(helper),
            "main verifier template should not carry duplicate quotient helper body {helper}"
        );
        assert!(
            !quotient_evaluator_template.contains(helper),
            "external evaluator template should not carry duplicate quotient helper body {helper}"
        );
    }
}

#[test]
fn batch_invert_handles_empty_and_singleton_ranges() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains("let count_bytes := sub(mptr_end, mptr_start)"),
        "batch inversion must compute the requested range length"
    );
    assert!(
        verifier_template.contains("if iszero(count_bytes) { leave }"),
        "empty batch inversion ranges should be a no-op"
    );
    assert!(
        verifier_template.contains("if eq(count_bytes, 0x20)"),
        "singleton batch inversion ranges need a dedicated path"
    );
    assert!(
        verifier_template.contains("if ret { mstore(mptr_start, mload(single_scratch)) }"),
        "singleton batch inversion must store the single inverse in place"
    );
}

#[test]
fn production_verifier_documents_revert_or_true_policy() {
    let verifier_template = verifier_template_corpus();

    assert!(
        verifier_template.contains("success-or-revert"),
        "verifyProof NatSpec must document invalid-proof failure semantics"
    );
    assert!(
        !verifier_template.contains("InvalidVerifierDependency"),
        "constructor pinning removes per-call dependency preflight code"
    );
    assert!(
        !verifier_template.contains("return false;"),
        "generated verifier should not mix false returns with revert-on-invalid semantics"
    );
    assert!(
        !verifier_template.contains("mstore(0x00, success)"),
        "generated verifier must not return a false boolean on invalid proofs"
    );
    assert!(
            verifier_template.contains("function ec_pairing(success, lhs_mptr, rhs_mptr) -> ret")
                && verifier_template
                    .contains("ret := success\n                if iszero(ret) { leave }")
                && verifier_template.contains(
                    "ret := and(ret, eq(mload(scratch), 1))\n                if iszero(ret) { revert(0, 0) }\n                ret := 1",
                ),
            "final pairing helper must revert on pairing failure and normalize success to one"
        );
    assert!(
        verifier_template
            .contains("success := ec_pairing(success, PAIRING_RHS_MPTR, PAIRING_LHS_MPTR)"),
        "final epilogue must route the pairing check through the reverting helper"
    );
    assert!(
        !verifier_template.contains("return(0x00, 0x20)\n            {%- else %}"),
        "trace and production epilogues must not diverge into false-return semantics"
    );
    assert!(
        verifier_template.contains("mstore(RETURN_MPTR, 1)\n            return(RETURN_MPTR, 0x20)"),
        "generated verifier must only return literal true after the reverting pairing helper"
    );
}

#[test]
fn templates_do_not_write_solidity_reserved_memory_slots() {
    let verifier_template = verifier_template_corpus();
    let quotient_template = include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol");
    let quotient_helpers =
        include_str!("../../templates/partials/quotient_numerator/QuotientHelpers.yul");
    let vk_template = include_str!("../../templates/contracts/Halo2VerifyingKey.sol");
    let pcs_source = include_str!("kzg/mod.rs");

    for (name, source) in [
        ("Halo2Verifier.sol", verifier_template),
        ("Halo2QuotientEvaluator.sol", quotient_template),
        ("QuotientHelpers.yul", quotient_helpers),
        ("Halo2VerifyingKey.sol", vk_template),
    ] {
        for needle in [
            "mstore(0,",
            "mstore(0x00,",
            "mstore(0x20,",
            "mstore(0x40,",
            "mstore(0x60,",
            "mstore(add(0x00,",
            "mstore(add(0x20,",
            "mstore(add(0x40,",
            "mstore(add(0x60,",
            "mcopy(0x00,",
            "mcopy(0x20,",
            "mcopy(0x40,",
            "mcopy(0x60,",
            "calldatacopy(0x00,",
            "calldatacopy(0x20,",
            "calldatacopy(0x40,",
            "calldatacopy(0x60,",
            "return(0x00,",
        ] {
            assert!(
                    !source.contains(needle),
                    "{name} must not write or return from Solidity-reserved memory words: found {needle}"
                );
        }
    }
    assert!(
        !pcs_source.contains("mcopy(0x0,")
            && !pcs_source.contains("mstore(0,")
            && !pcs_source.contains(", 0x00, {G1_MSM_PAIR_BYTES:#x}")
            && !pcs_source.contains(", 0x00, {G1ADD_INPUT_BYTES:#x}"),
        "generated PCS helper scratch must not be rooted at memory 0"
    );
}

#[test]
fn templates_use_planned_memory_slots_for_theta_and_commitment_layout() {
    for (name, source) in [
        ("Halo2Verifier", verifier_template_corpus()),
        (
            "Halo2QuotientEvaluator",
            include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol"),
        ),
    ] {
        assert!(
            !source.contains("theta_mptr +"),
            "{name} should render named planned theta-relative slots"
        );
        assert!(
            !source.contains("comms_mptr_base +"),
            "{name} should render named planned commitment bases"
        );
    }
}

#[test]
fn final_msm_pair_count_is_a_codegen_assertion() {
    let source = include_str!("kzg/mod.rs");

    assert!(
        source.contains("pair_idx, final_msm_terms"),
        "PCS emission should compare emitted final MSM pairs with the planned shape"
    );
    assert!(
        source.contains("final MSM input term count changed during emission"),
        "PCS emission should fail loudly if final MSM shape and Yul emission diverge"
    );
    assert!(
        !source.contains("debug_assert_eq!(\n            pair_idx, final_msm_terms"),
        "final MSM shape mismatches must not be debug-only"
    );
}

#[test]
fn verify_proof_natspec_requires_application_binding() {
    let verifier_template = verifier_template_corpus();

    for required in [
        "checks only that `proof` verifies for the supplied public",
        "Application contracts must",
        "state roots",
        "program",
        "expected IVC outputs",
        "chain/domain separation",
    ] {
        assert!(
            verifier_template.contains(required),
            "verifyProof NatSpec must document application binding requirement: {required}"
        );
    }
    for required in [
        "/// @param proof Solidity-facing proof bytes",
        "/// @param instances Public instance scalars",
        "/// @return Always `true`",
    ] {
        assert!(
            verifier_template.contains(required),
            "verifyProof NatSpec must include ABI documentation: {required}"
        );
    }
}

#[test]
fn production_verifier_entrypoint_is_external_view() {
    let verifier_template = verifier_template_corpus();

    assert!(
            verifier_template.contains(") external {%- if self.trace || self.gas_checkpoints %} returns (bool) {%- else %} view returns (bool) {%- endif %}"),
            "generated verifyProof entrypoint should render as external view in production"
        );
    assert!(
        !verifier_template.contains(") public {%- if self.trace || self.gas_checkpoints %}"),
        "production verifier should not expose the calldata entrypoint as public"
    );
}

#[test]
fn midfall_comment_corpus_is_source_indexed_and_attributed() {
    let corpus = include_str!("../../docs/reference/MIDFALL_PROOFS_COMMENT_CORPUS.md");
    let extractor = include_str!("../../scripts/extract_midfall_comments.py");

    for required in [
        "# Midfall Proofs Comment Corpus",
        "Rust source files: `57`",
        "Comment lines: `3597`",
        "## `plonk/verifier.rs`",
        "## `plonk/linearization/verifier.rs`",
        "## `poly/kzg/mod.rs`",
        "## `transcript/implementors.rs`",
        "SPDX-License-Identifier: Apache-2.0",
        "License And Attribution",
    ] {
        assert!(
            corpus.contains(required),
            "Midfall comment corpus missing expected source-indexed content: {required}"
        );
    }

    for required in [
        "COMMENT_RE",
        "--check",
        "--write",
        "Git commit",
        "CommentBlock",
    ] {
        assert!(
            extractor.contains(required),
            "comment extractor should remain deterministic/checkable: {required}"
        );
    }
}

#[test]
fn solidity_templates_have_required_natspec_surface() {
    let verifier = verifier_template_corpus();
    let vk = include_str!("../../templates/contracts/Halo2VerifyingKey.sol");
    let quotient = include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol");

    for (name, source, contract) in [
        ("verifier", verifier, "contract Halo2Verifier"),
        ("verifying key", vk, "contract Halo2VerifyingKey"),
        (
            "quotient evaluator",
            quotient,
            "contract Halo2QuotientEvaluator",
        ),
    ] {
        assert!(
            source.contains("/// @title")
                && source.contains("/// @notice")
                && source.contains("/// @dev"),
            "{name} template should have contract-level NatSpec"
        );
        assert!(
            source.contains(contract),
            "{name} template should still declare {contract}"
        );
    }

    for required in [
        "/// @notice Verifying-key contract address",
        "checked at construction time",
        "/// @notice Quotient evaluator contract",
        "/// @param authorizedVk",
        "/// @param authorizedQuotient",
        "/// @return Always `true`",
    ] {
        assert!(
            verifier.contains(required),
            "verifier NatSpec missing required declaration docs: {required}"
        );
    }
    assert!(
        vk.contains("/// @notice Deploy the verifying-key payload"),
        "VK constructor should have NatSpec"
    );
    assert!(
        quotient.contains("/// @notice Evaluate the generated quotient numerator block"),
        "quotient fallback should have NatSpec"
    );
}

#[test]
fn midfall_comment_ports_reference_rust_sources() {
    let verifier = verifier_template_corpus();
    let quotient = include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol");
    let quotient_helpers =
        include_str!("../../templates/partials/quotient_numerator/QuotientHelpers.yul");
    let numerator =
        include_str!("../../templates/partials/quotient_numerator/QuotientNumeratorBlock.yul");
    let lowering = lowering_source_corpus();
    let evaluator = include_str!("quotient_numerator/yul_emit.rs");
    let protocol = include_str!("protocol/mod.rs");
    let pcs = include_str!("kzg/mod.rs");
    let spec = include_str!("../../docs/reference/HALO2_MIDNIGHT_VERIFIER_SPEC.md");

    for required in [
        "midfall/proofs/src/plonk/verifier.rs",
        "midfall/proofs/src/transcript/implementors.rs",
        "midfall/proofs/src/poly/kzg/mod.rs",
    ] {
        assert!(
            verifier.contains(required) || spec.contains(required),
            "verifier docs should reference upstream Rust source: {required}"
        );
    }
    for required in [
        "midfall/proofs/src/plonk/mod.rs::partially_evaluate_identities",
        "midfall/proofs/src/plonk/linearization/verifier.rs::compute_linearization_commitment",
        "selectors do not appear as normal proof eval scalars",
    ] {
        assert!(
            quotient.contains(required)
                || quotient_helpers.contains(required)
                || numerator.contains(required),
            "quotient docs should carry adapted upstream comments: {required}"
        );
    }
    assert!(
        verifier.contains("Hashable<Keccak256> for G1Projective")
            || spec.contains("Hashable<Keccak256> for G1Projective"),
        "transcript docs should reference upstream point hashing comments"
    );
    assert!(
        protocol.contains("counterpart of the iterator-heavy verifier"),
        "protocol plan should document the Midfall verifier-flow port"
    );
    for required in [
        "committed instances and normal (non-committed) instances",
        "Fixed evals are query-based proof reads",
        "absorbs this `transcript_repr` digest",
    ] {
        assert!(
            lowering.contains(required),
            "generator should carry adapted verifier comment: {required}"
        );
    }
    for required in [
        "Hash the prover's advice commitments",
        "Read commitment(s) to the quotient polynomial h(X)=nu(X)/(X^n-1)",
        "Queries corresponding to simple, multiplicative selectors need not be",
        "omega^rotation*x",
    ] {
        assert!(
            protocol.contains(required),
            "protocol plan should carry adapted verifier comment: {required}"
        );
    }
    for required in [
        "partially_evaluate_identities",
        "LogUp emitter",
        "Permutation emitter",
        "Trashcan emitter",
    ] {
        assert!(
            evaluator.contains(required),
            "quotient evaluator codegen should carry adapted verifier comment: {required}"
        );
    }
    assert!(
        pcs.contains("Upstream comments ported here")
            && pcs.contains("Sort point sets by ascending cardinality")
            && pcs.contains("Sample a challenge x_3")
            && pcs.contains("Scale z*pi - vG"),
        "PCS emitter should document the KZG comment port"
    );
}

#[test]
fn gas_checkpoints_are_debug_only_template_paths() {
    let verifier_template = verifier_template_corpus();
    let lib_source = include_str!("../lib.rs");

    assert!(
            verifier_template.contains("{%- if self.gas_checkpoints %}\n            // Section-boundary gas-attribution checkpoint"),
            "gas checkpoint helper must be guarded by the gas-checkpoint template flag"
        );
    assert_eq!(
        verifier_template.matches("gas_checkpoint(").count(),
        verifier_template.matches("{%- if self.gas_checkpoints").count(),
        "every gas_checkpoint definition/call should have its own self.gas_checkpoints guard"
    );
    assert!(
            verifier_template.contains(") external {%- if self.trace || self.gas_checkpoints %} returns (bool) {%- else %} view returns (bool) {%- endif %}"),
            "production renders should stay external view unless trace/gas logs are enabled"
        );
    assert!(
        lib_source.contains("pub const SOLIDITY_GAS_CHECKPOINTS_ENABLED"),
        "gas checkpoints should remain an explicit feature flag"
    );
    assert!(
            lib_source.contains(
                "pub const SOLIDITY_GAS_CHECKPOINTS_ENABLED: bool = cfg!(feature = \"solidity-gas-checkpoints\");"
            ),
            "default renders should allow gas checkpoints without trace/profiling logs"
    );
    assert!(
        lib_source.contains("RenderDiagnostics { gas_checkpoints: true, .. }"),
        "docs should call out the explicit benchmarking render knob"
    );
}

#[test]
fn trash_challenge_is_squeezed_even_without_trash_arguments() {
    let verifier_template = verifier_template_corpus();
    let squeeze = verifier_template
        .find("buf_len := squeeze_to(buf_len, TRASH_CHALLENGE_MPTR)")
        .expect("trash challenge squeeze should be rendered");
    let trash_guard = verifier_template
        .find("{%- if num_trashcans != 0 %}\n            // ---- trashcans ----")
        .expect("trashcan commitment reads should still be guarded");

    assert!(
            squeeze < trash_guard,
            "Midnight squeezes trash_challenge unconditionally; only trashcan commitment reads may be guarded"
        );
}

#[test]
fn truncated_challenge_comments_cover_x1_x4_power_masks() {
    let verifier_template = verifier_template_corpus();
    let pcs_codegen = include_str!("kzg/mod.rs");

    assert!(
        verifier_template.contains("x1 and x4 remain full squeezed Fr words"),
        "x3 squeeze comment must clarify that x1/x4 are handled by truncated powers"
    );
    assert!(
        verifier_template.contains("truncate(x1^i) and truncate(x4^i)"),
        "verifier template should document the PCS power truncation rule"
    );
    assert!(
        pcs_codegen.contains("proofs/src/poly/kzg/mod.rs computes"),
        "x1 power generation should point back to the Rust verifier source"
    );
    assert!(
        pcs_codegen.contains("power[i] = truncate(x1^i)"),
        "x1 power generation should document truncated_powers(x1)"
    );
    assert!(
        pcs_codegen.contains("truncated_powers(x4)[i] = truncate(x4^i)"),
        "x4 power generation should document truncated_powers(x4)"
    );
    assert!(
        pcs_codegen.contains("mstore(p, and(acc, {TRUNC_MASK_128}))"),
        "x1 emitted powers must be masked under truncated-challenges"
    );
    assert!(
        pcs_codegen.contains("let x4_pow_{s} := and(x4_pow_full, {TRUNC_MASK_128})"),
        "x4 emitted powers must be masked under truncated-challenges"
    );
}

#[test]
fn generated_heavy_assemblies_keep_memory_safe_for_via_ir() {
    for (name, source) in [
        ("Halo2Verifier.sol", verifier_template_corpus()),
        (
            "Halo2QuotientEvaluator.sol",
            include_str!("../../templates/contracts/Halo2QuotientEvaluator.sol"),
        ),
    ] {
        assert!(
            source.contains("assembly (\"memory-safe\")"),
            "{name} needs memory-safe assembly annotations for solc via-IR stack allocation"
        );
    }
}

#[test]
fn generator_restriction_errors_are_typed() {
    assert_eq!(
        SolidityGenerator::SUPPORTED_COMMITTED_INSTANCE_COMMITMENT,
        CommittedInstanceCommitmentKind::Identity
    );
    assert_eq!(
            GeneratorError::UnsupportedInstanceColumnShape {
                total: 2,
                committed: 0,
                expected_committed: 1,
                expected_non_committed: 1,
            }
            .to_string(),
            "unsupported instance column shape: got total=2, committed=0, non_committed=2; expected exactly 1 identity-committed and 1 non-committed"
        );
    assert_eq!(
            GeneratorError::UnsupportedInstanceColumnShape {
                total: 1,
                committed: 2,
                expected_committed: 1,
                expected_non_committed: 1,
            }
            .to_string(),
            "unsupported instance column shape: got total=1, committed=2, non_committed=invalid: committed 2 exceeds total 1; expected exactly 1 identity-committed and 1 non-committed"
        );
    assert_eq!(
        GeneratorError::RotatedInstanceQuery {
            column: 1,
            rotation: -1,
        }
        .to_string(),
        "rotated instance query is not supported: column 1, rotation -1"
    );
    assert_eq!(
            GeneratorError::UnsupportedAccumulatorEncoding {
                offset: 5,
                num_limbs: 7,
                num_limb_bits: 56,
                num_instances: 14,
                reason: "accumulator public-input tail exceeds num_instances",
            }
            .to_string(),
            "unsupported accumulator encoding: offset=5, num_limbs=7, num_limb_bits=56, num_instances=14; accumulator public-input tail exceeds num_instances"
        );
    let stale = ["not", " yet ", "implemented"].concat();
    assert!(
        !include_str!("mod.rs").contains(&stale),
        "unsupported verifier shapes should be surfaced as GeneratorError values"
    );
}

#[test]
fn permutation_delta_literal_is_computed_from_field_constant() {
    let computed = u256_string(fe_to_u256::<Fq>(&Fq::DELTA));

    assert_eq!(fr_delta_literal(), computed);
    assert!(
        !include_str!("mod.rs").contains(&computed),
        "codegen source should not hard-code the current Fr::DELTA decimal/hex literal"
    );
}

#[test]
fn verifier_template_omits_dead_constants_and_ec_helpers() {
    let verifier_template = verifier_template_corpus();

    for stale in [
        "FIRST_QUOTIENT_X_CPTR",
        "LAST_QUOTIENT_X_CPTR",
        "G1_SCALAR_MPTR",
        "function ec_add_acc",
        "function ec_mul_acc",
        "function ec_add_tmp",
        "function ec_mul_tmp",
    ] {
        assert!(
            !verifier_template.contains(stale),
            "production verifier template should not keep dead helper/constant: {stale}"
        );
    }
}

#[test]
fn expression_lowering_matches_quotient_vm_eval() {
    let mut cs = ConstraintSystem::default();
    let advice = cs.advice_column();
    let fixed = cs.fixed_column();
    let instance = cs.instance_column();
    let challenge = cs.challenge_usable_after(FirstPhase);
    cs.create_gate("typed lowering", |meta| {
        let a = meta.query_advice(advice, Rotation::next());
        let f = meta.query_fixed(fixed, Rotation::prev());
        let i = meta.query_instance(instance, Rotation::cur());
        let c = meta.query_challenge(challenge);
        let seven = Expression::Constant(Fq::from(7u64));
        Constraints::without_selector(vec![(
            "typed lowering",
            a.clone() * f.clone() + i.clone() * c.clone() + seven * a - f,
        )])
    });
    let expr = cs.gates()[0].polynomials()[0].clone();

    let mut values = HashMap::new();
    values.insert(0x100, Fq::from(11u64));
    values.insert(0x120, Fq::from(13u64));
    values.insert(0x140, Fq::from(17u64));
    values.insert(0x160, Fq::from(19u64));

    let mut env = TestQuotientExpressionEnv::default();
    env.advice.insert(
        (advice.index(), 1),
        QuotientExpr::Mem(QuotientMem::Literal(0x100)),
    );
    env.fixed.insert(
        (fixed.index(), -1),
        QuotientExpr::Mem(QuotientMem::Literal(0x120)),
    );
    env.instance.insert(
        (instance.index(), 0),
        QuotientExpr::Mem(QuotientMem::Literal(0x140)),
    );
    env.challenges.insert(
        challenge.index(),
        QuotientExpr::Mem(QuotientMem::Literal(0x160)),
    );

    let expected = expr.evaluate(
        &|scalar| scalar,
        &|_| panic!("test expression should not contain selectors"),
        &|_query| values[&0x120],
        &|query| {
            assert_eq!(query.rotation(), Rotation::next());
            values[&0x100]
        },
        &|query| {
            assert_eq!(query.rotation(), Rotation::cur());
            values[&0x140]
        },
        &|_| values[&0x160],
        &|inner| -inner,
        &|lhs, rhs| lhs + rhs,
        &|lhs, rhs| lhs * rhs,
        &|inner, scalar| inner * scalar,
    );

    let lowered = quotient_expr_from_expression(&env, &expr);
    let mut builder = QuotientProgramBuilder::default();
    builder.emit_expr(&lowered);
    let actual = eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values);
    assert_eq!(actual, expected);
}

#[test]
fn quotient_vm_lin7_matches_direct_expr_eval() {
    let mut values = HashMap::new();
    let mut expr = QuotientExpr::Const(U256::ZERO);
    for i in 0..7u32 {
        let ptr = 0x300 + i * 0x20;
        values.insert(ptr, Fq::from(11 + i as u64));
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(3 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[0], Q_OP_LIN7);
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_bilin7_row_matches_direct_expr_eval() {
    let lhs = 0x440;
    let mut values = HashMap::new();
    values.insert(lhs, Fq::from(29u64));
    let mut expr = QuotientExpr::Const(U256::ZERO);
    for i in 0..7u32 {
        let rhs = 0x500 + i * 0x20;
        values.insert(rhs, Fq::from(37 + i as u64));
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(5 + i as u64),
                quotient_mul_expr(
                    QuotientExpr::Mem(QuotientMem::Literal(lhs)),
                    QuotientExpr::Mem(QuotientMem::Literal(rhs)),
                ),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[0], Q_OP_BILIN7_ROW);
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_bilin7_pairwise_matches_direct_expr_eval() {
    let lhs_base = 0x620;
    let rhs_base = 0x820;
    let mut values = HashMap::new();
    for i in 0..7u32 {
        values.insert(lhs_base + i * 0x20, Fq::from(41 + i as u64));
        values.insert(rhs_base + i * 0x20, Fq::from(71 + i as u64));
    }

    let mut expr = QuotientExpr::Const(U256::ZERO);
    for i in 0..7u32 {
        for j in 0..7u32 {
            expr = quotient_add_expr(
                expr,
                quotient_scale_expr(
                    Fq::from(9 + i as u64 + j as u64),
                    quotient_mul_expr(
                        QuotientExpr::Mem(QuotientMem::Literal(lhs_base + i * 0x20)),
                        QuotientExpr::Mem(QuotientMem::Literal(rhs_base + j * 0x20)),
                    ),
                ),
            );
        }
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[0], Q_OP_BILIN7_PAIRWISE);
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_limb_decomposition_survives_const_table_overflow() {
    // A large affine sum over consecutive limb pointers is emitted as a chain of
    // LIN7 opcodes whose coefficients land in the one-byte constant table. With
    // more than 256 distinct coefficients the table overflows a `u8` slot
    // partway through emission. Before the fix, `emit_limb_shape`'s
    // `u8::try_from(slot).expect(...)` panicked once the shape being emitted was
    // preceded by enough residue constants; the decomposition path now re-checks
    // the post-residue table and falls back to generic ops for the overflowing
    // shape. This exercises that fallback and confirms it still evaluates the
    // expression correctly.
    let term_count = 300u32;
    let mut values = HashMap::new();
    let mut expr = QuotientExpr::Const(U256::ZERO);
    for k in 0..term_count {
        let ptr = 0x1000 + k * 0x20;
        values.insert(ptr, Fq::from(17 + k as u64));
        expr = quotient_add_expr(
            expr,
            // Coefficient `k + 2` keeps every term scaled (coeff 1 would drop the
            // constant) and distinct, so the table grows one slot per term.
            quotient_scale_expr(
                Fq::from(k as u64 + 2),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    // The pre-fix builder panics inside this call for this input.
    builder.emit_expr(&expr);

    assert!(
        builder.consts.len() > u8::MAX as usize,
        "test must overflow the one-byte constant table to exercise the fallback"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_pow5_matches_direct_expr_eval() {
    let ptr = 0xa20;
    let mut values = HashMap::new();
    values.insert(ptr, Fq::from(131u64));
    let base = QuotientExpr::Mem(QuotientMem::Literal(ptr));
    let expr = quotient_mul_expr(
        quotient_mul_expr(base.clone(), base.clone()),
        quotient_mul_expr(base.clone(), quotient_mul_expr(base.clone(), base)),
    );

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::default();
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[3], Q_OP_POW5);
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_pow5_rejects_near_miss_product_shapes() {
    let a_ptr = 0xa60;
    let b_ptr = 0xa80;
    let mut values = HashMap::new();
    values.insert(a_ptr, Fq::from(137u64));
    values.insert(b_ptr, Fq::from(139u64));

    let a = QuotientExpr::Mem(QuotientMem::Literal(a_ptr));
    let b = QuotientExpr::Mem(QuotientMem::Literal(b_ptr));
    let a4_times_b = quotient_mul_expr(
        quotient_mul_expr(quotient_mul_expr(a.clone(), a.clone()), a.clone()),
        quotient_mul_expr(a, b),
    );

    let expected = eval_quotient_expr_for_test(&a4_times_b, &values);
    let mut builder = QuotientProgramBuilder::default();
    builder.emit_expr(&a4_times_b);

    assert!(
        !builder.bytes.contains(&Q_OP_POW5),
        "a^4 * b must not be compressed as a POW5"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_add_product_reserves_scalar_before_base_constants() {
    let lhs = 0xaa0;
    let rhs = 0xac0;
    let mut values = HashMap::new();
    values.insert(lhs, Fq::from(149u64));
    values.insert(rhs, Fq::from(157u64));

    let mut base = QuotientExpr::Const(U256::ZERO);
    for value in 1..=255u64 {
        base = quotient_add_expr(base, QuotientExpr::Const(U256::from(value)));
    }
    let product = quotient_mul_expr(
        quotient_mul_expr(
            QuotientExpr::Mem(QuotientMem::Literal(lhs)),
            QuotientExpr::Mem(QuotientMem::Literal(rhs)),
        ),
        QuotientExpr::Const(U256::from(300u64)),
    );
    let expr = quotient_add_expr(base, product);

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::default();
    builder.emit_expr(&expr);

    assert!(
        builder.bytes.contains(&Q_OP_ADD_MUL_MEM_MEM_CONST_U8),
        "product should stay on the fused add-mul path"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_limb_subshape_matches_direct_expr_eval() {
    let mut values = HashMap::new();
    let mut expr = QuotientExpr::Const(U256::ZERO);
    let residue = quotient_mul_expr(
        QuotientExpr::Mem(QuotientMem::Literal(0xc00)),
        quotient_mul_expr(
            QuotientExpr::Mem(QuotientMem::Literal(0xc20)),
            QuotientExpr::Mem(QuotientMem::Literal(0xc40)),
        ),
    );
    values.insert(0xc00, Fq::from(211u64));
    values.insert(0xc20, Fq::from(223u64));
    values.insert(0xc40, Fq::from(227u64));

    for i in 0..7u32 {
        let ptr = 0xb00 + i * 0x20;
        values.insert(ptr, Fq::from(151 + i as u64));
        if i == 1 {
            expr = quotient_add_expr(expr, QuotientExpr::Const(U256::from(9u64)));
        }
        if i == 4 {
            expr = quotient_add_expr(expr, residue.clone());
        }
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(19 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert!(
        builder.bytes.contains(&Q_OP_LIN7),
        "larger affine sums should still extract LIN7 subshapes"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_limb_decomposition_reserves_shape_coeffs_before_residue() {
    let mut values = HashMap::new();
    let mut expr = QuotientExpr::Const(U256::ZERO);

    for i in 0..7u32 {
        let ptr = 0xb00 + i * WORD_BYTES as u32;
        values.insert(ptr, Fq::from(151 + i as u64));
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(19 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    for i in 0..256u32 {
        let ptr = 0x2000 + i * 0x40;
        values.insert(ptr, Fq::from(401 + i as u64));
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(1000 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert!(
        builder.consts.len() > u8::MAX as usize,
        "residue should grow the constant table past u8"
    );
    assert!(
        builder.bytes.contains(&Q_OP_LIN7),
        "larger affine sums should still extract LIN7 subshapes"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_limb_subshape_inside_conditional_product_matches_direct_expr_eval() {
    let mut values = HashMap::new();
    let cond_ptr = 0xd00;
    values.insert(cond_ptr, Fq::from(3u64));
    let mut inner = QuotientExpr::Const(U256::ZERO);
    for i in 0..7u32 {
        let ptr = 0xe00 + i * 0x20;
        values.insert(ptr, Fq::from(251 + i as u64));
        if i == 2 {
            inner = quotient_add_expr(inner, QuotientExpr::Const(U256::from(17u64)));
        }
        inner = quotient_add_expr(
            inner,
            quotient_scale_expr(
                Fq::from(31 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }
    let expr = quotient_mul_expr(QuotientExpr::Mem(QuotientMem::Literal(cond_ptr)), inner);

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert!(
        builder.bytes.contains(&Q_OP_MODARITH7),
        "conditional affine factors should collapse into the fused mod-arith opcode"
    );
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_modarith7_mixed_affine_matches_direct_expr_eval() {
    let lhs_base = 0xf00;
    let rhs_base = 0x1100;
    let lin_base = 0x1300;
    let factored_lin_base = 0x1700;
    let cond = 0x1500;
    let scalar = 0x1520;
    let product_lhs = 0x1540;
    let product_rhs = 0x1560;
    let mut values = HashMap::new();
    values.insert(cond, Fq::from(3u64));
    values.insert(scalar, Fq::from(5u64));
    values.insert(product_lhs, Fq::from(11u64));
    values.insert(product_rhs, Fq::from(13u64));
    for i in 0..7u32 {
        values.insert(lhs_base + i * WORD_BYTES as u32, Fq::from(7 + i as u64));
        values.insert(rhs_base + i * WORD_BYTES as u32, Fq::from(17 + i as u64));
        values.insert(lin_base + i * WORD_BYTES as u32, Fq::from(29 + i as u64));
        values.insert(
            factored_lin_base + i * WORD_BYTES as u32,
            Fq::from(31 + i as u64),
        );
    }

    let mut inner = QuotientExpr::Const(U256::from(41u64));
    for i in 0..7u32 {
        inner = quotient_add_expr(
            inner,
            quotient_scale_expr(
                Fq::from(43 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(lin_base + i * WORD_BYTES as u32)),
            ),
        );
    }
    let mut factored_lin = QuotientExpr::Const(U256::ZERO);
    for i in 0..7u32 {
        factored_lin = quotient_add_expr(
            factored_lin,
            quotient_scale_expr(
                Fq::from(47 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(
                    factored_lin_base + i * WORD_BYTES as u32,
                )),
            ),
        );
    }
    inner = quotient_add_expr(
        inner,
        quotient_mul_expr(QuotientExpr::Mem(QuotientMem::Literal(cond)), factored_lin),
    );
    for i in 0..7u32 {
        for j in 0..7u32 {
            inner = quotient_add_expr(
                inner,
                quotient_scale_expr(
                    Fq::from(53 + i as u64 + j as u64),
                    quotient_mul_expr(
                        QuotientExpr::Mem(QuotientMem::Literal(lhs_base + i * WORD_BYTES as u32)),
                        QuotientExpr::Mem(QuotientMem::Literal(rhs_base + j * WORD_BYTES as u32)),
                    ),
                ),
            );
        }
    }
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(97u64),
            QuotientExpr::Mem(QuotientMem::Literal(scalar)),
        ),
    );
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(101u64),
            quotient_mul_expr(
                QuotientExpr::Mem(QuotientMem::Literal(product_lhs)),
                QuotientExpr::Mem(QuotientMem::Literal(product_rhs)),
            ),
        ),
    );
    let expr = quotient_mul_expr(QuotientExpr::Mem(QuotientMem::Literal(cond)), inner);

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[0], Q_OP_MODARITH7);
    assert_eq!(quotient_op_len(&builder.bytes, 0), builder.bytes.len());
    let (ops, mem_tokens) = quotient_program_usage(&builder.bytes);
    assert_eq!(ops, vec![Q_OP_MODARITH7]);
    assert!(mem_tokens.is_empty());
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_vm_modarith7_sparse_affine_product_matches_direct_expr_eval() {
    let cond = 0x1800;
    let linear = 0x1820;
    let lhs0 = 0x1840;
    let rhs0 = 0x1860;
    let lhs1 = 0x1880;
    let rhs1 = 0x18a0;
    let factored0 = 0x18c0;
    let factored1 = 0x18e0;
    let mut values = HashMap::new();
    values.insert(cond, Fq::from(3u64));
    values.insert(linear, Fq::from(5u64));
    values.insert(lhs0, Fq::from(7u64));
    values.insert(rhs0, Fq::from(11u64));
    values.insert(lhs1, Fq::from(13u64));
    values.insert(rhs1, Fq::from(17u64));
    values.insert(factored0, Fq::from(19u64));
    values.insert(factored1, Fq::from(23u64));

    let mut inner = QuotientExpr::Const(U256::from(19u64));
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(23u64),
            QuotientExpr::Mem(QuotientMem::Literal(linear)),
        ),
    );
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(29u64),
            quotient_mul_expr(
                QuotientExpr::Mem(QuotientMem::Literal(lhs0)),
                QuotientExpr::Mem(QuotientMem::Literal(rhs0)),
            ),
        ),
    );
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(31u64),
            quotient_mul_expr(
                QuotientExpr::Mem(QuotientMem::Literal(lhs1)),
                QuotientExpr::Mem(QuotientMem::Literal(rhs1)),
            ),
        ),
    );
    let factored = quotient_add_expr(
        QuotientExpr::Const(U256::from(37u64)),
        quotient_add_expr(
            quotient_scale_expr(
                Fq::from(41u64),
                QuotientExpr::Mem(QuotientMem::Literal(factored0)),
            ),
            quotient_scale_expr(
                Fq::from(43u64),
                QuotientExpr::Mem(QuotientMem::Literal(factored1)),
            ),
        ),
    );
    inner = quotient_add_expr(
        inner,
        quotient_scale_expr(
            Fq::from(47u64),
            quotient_mul_expr(QuotientExpr::Mem(QuotientMem::Literal(cond)), factored),
        ),
    );
    let expr = quotient_mul_expr(QuotientExpr::Mem(QuotientMem::Literal(cond)), inner);

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_eq!(builder.bytes[0], Q_OP_MODARITH7);
    assert_eq!(quotient_op_len(&builder.bytes, 0), builder.bytes.len());
    let (ops, mem_tokens) = quotient_program_usage(&builder.bytes);
    assert_eq!(ops, vec![Q_OP_MODARITH7]);
    assert!(mem_tokens.is_empty());
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn unmatched_limb_shape_falls_back_to_existing_vm_ops() {
    let mut values = HashMap::new();
    let mut expr = QuotientExpr::Const(U256::ZERO);
    for i in 0..6u32 {
        let ptr = 0x980 + i * 0x20;
        values.insert(ptr, Fq::from(101 + i as u64));
        expr = quotient_add_expr(
            expr,
            quotient_scale_expr(
                Fq::from(17 + i as u64),
                QuotientExpr::Mem(QuotientMem::Literal(ptr)),
            ),
        );
    }

    let expected = eval_quotient_expr_for_test(&expr, &values);
    let mut builder = QuotientProgramBuilder::with_limb_vm_ops(true);
    builder.emit_expr(&expr);

    assert_ne!(builder.bytes[0], Q_OP_LIN7);
    assert_eq!(
        eval_quotient_vm_for_test(&builder.bytes, &builder.consts, &values),
        expected
    );
}

#[test]
fn quotient_program_usage_tracks_byte_ops_and_tokens() {
    let bytes = vec![
        Q_OP_PUSH_MEM_TOKEN,
        Q_MEM_THETA,
        Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
        0x00,
        0x02,
        0x00,
        0x20,
        0x03,
        0x00,
        0x40,
        0x04,
        Q_OP_FOLD_MAIN,
    ];

    let (ops, mem_tokens) = quotient_program_usage(&bytes);

    assert!(ops.contains(&Q_OP_PUSH_MEM_TOKEN));
    assert!(ops.contains(&Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16));
    assert!(ops.contains(&Q_OP_FOLD_MAIN));
    assert!(!ops.contains(&Q_OP_ADD_MUL_CONST_U8_MEM_U16));
    assert_eq!(mem_tokens, vec![Q_MEM_THETA]);
}

/// Test helper for constructing quotient addition expressions.
fn quotient_add_expr(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Add(Box::new(lhs), Box::new(rhs))
}

/// Test helper for constructing quotient multiplication expressions.
fn quotient_mul_expr(lhs: QuotientExpr, rhs: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Mul(Box::new(lhs), Box::new(rhs))
}

/// Test helper for attaching an Fr coefficient to a quotient expression.
fn quotient_scale_expr(coeff: Fq, expr: QuotientExpr) -> QuotientExpr {
    QuotientExpr::Mul(
        Box::new(QuotientExpr::Const(fe_to_u256::<Fq>(&coeff))),
        Box::new(expr),
    )
}

/// Construct a synthetic identity with a zero expression.
fn test_quotient_identity(
    global_index: usize,
    source: QuotientIdentitySource,
    target: QuotientTarget,
) -> QuotientIdentity {
    QuotientIdentity {
        meta: QuotientIdentityMetadata {
            global_index,
            source,
        },
        lines: Vec::new(),
        var: "eval".to_string(),
        target,
        expr: QuotientExpr::Const(U256::ZERO),
    }
}

/// Construct a synthetic identity backed by an explicit expression.
fn test_quotient_identity_with_expr(
    global_index: usize,
    target: QuotientTarget,
    expr: QuotientExpr,
) -> QuotientIdentity {
    QuotientIdentity {
        meta: QuotientIdentityMetadata {
            global_index,
            source: QuotientIdentitySource::Gate {
                gate_index: global_index,
                gate_name: format!("synthetic_gate_{global_index}"),
                constraint_index: 0,
                constraint_name: "synthetic_constraint".to_string(),
                polynomial_index: 0,
            },
        },
        lines: Vec::new(),
        var: format!("eval_{global_index}"),
        target,
        expr,
    }
}

/// Build a quotient execution plan fixture while deriving selector fold data.
fn test_quotient_execution_plan(
    expected: Vec<QuotientIdentity>,
    inline_identities: Vec<QuotientIdentity>,
    items: Vec<QuotientProgramItem>,
    native_identities: Vec<QuotientIdentity>,
    native_permutation_identities: Vec<QuotientIdentity>,
    native_lookup_identities: Vec<QuotientIdentity>,
    structured_tail_identities: Vec<QuotientIdentity>,
) -> QuotientProgramPlan {
    let selector_count = expected
        .iter()
        .filter_map(|identity| match identity.target {
            QuotientTarget::Main => None,
            QuotientTarget::Selector(selector_idx) => Some(selector_idx + 1),
        })
        .max()
        .unwrap_or(0);
    let has_native_permutation =
        items.iter().any(|item| matches!(item, QuotientProgramItem::NativePermutation));
    let has_native_lookup =
        items.iter().any(|item| matches!(item, QuotientProgramItem::NativeLookup));
    QuotientProgramPlan {
        inline_identities,
        items,
        native_identities,
        native_permutation_identities,
        native_lookup_identities,
        structured_tail_identities,
        sorted_simple: (0..selector_count).collect(),
        has_native_permutation,
        has_native_lookup,
        selector_fold: VerifierBuildInputs::selector_fold_plan(&expected, selector_count),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TestQuotientBytecodeEvent {
    Fold(QuotientTarget),
    NativePermutation,
    NativeLookup,
    NativeIdentity(usize),
}

/// Extract high-level fold/native events from test bytecode.
fn quotient_bytecode_events_for_test(bytes: &[u8]) -> Vec<TestQuotientBytecodeEvent> {
    let mut events = Vec::new();
    let mut idx = 0usize;
    while idx < bytes.len() {
        match bytes[idx] {
            Q_OP_FOLD_MAIN => {
                events.push(TestQuotientBytecodeEvent::Fold(QuotientTarget::Main));
                idx += 1;
            }
            Q_OP_FOLD_SELECTOR => {
                events.push(TestQuotientBytecodeEvent::Fold(QuotientTarget::Selector(
                    bytes[idx + 1] as usize,
                )));
                idx += 4;
            }
            Q_OP_NATIVE_PERMUTATION => {
                events.push(TestQuotientBytecodeEvent::NativePermutation);
                idx += 1;
            }
            Q_OP_NATIVE_LOOKUP => {
                events.push(TestQuotientBytecodeEvent::NativeLookup);
                idx += 1;
            }
            Q_OP_NATIVE_IDENTITY => {
                events.push(TestQuotientBytecodeEvent::NativeIdentity(
                    read_u16(bytes, idx + 1) as usize,
                ));
                idx += 3;
            }
            op => {
                let len = quotient_opcode_byte_len(op)
                    .unwrap_or_else(|| panic!("dynamic test opcode {op:#x} at byte {idx}"));
                idx += len;
            }
        }
    }
    events
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestIdentityTraceEntry {
    global_index: usize,
    target: QuotientTarget,
    value: Fq,
    y_power: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TestLinearizationArtifacts {
    identity_trace: Vec<TestIdentityTraceEntry>,
    main_numerator: Fq,
    selector_buckets: Vec<Fq>,
    quotient_expected_eval: Fq,
}

/// Small exponentiation helper for expected linearization powers.
fn fq_pow(base: Fq, exp: usize) -> Fq {
    (0..exp).fold(Fq::ONE, |acc, _| acc * base)
}

/// Evaluate expected quotient linearization artifacts directly from identities.
fn expected_linearization_artifacts_for_test(
    identities: &[QuotientIdentity],
    mem: &HashMap<u32, Fq>,
    y: Fq,
    selector_count: usize,
) -> TestLinearizationArtifacts {
    let mut identity_trace = Vec::with_capacity(identities.len());
    let mut main_numerator = Fq::ZERO;
    let mut selector_buckets = vec![Fq::ZERO; selector_count];
    let total = identities.len();

    for identity in identities {
        let value = eval_quotient_expr_for_test(&identity.expr, mem);
        let y_power = total - 1 - identity.meta.global_index;
        let scaled = value * fq_pow(y, y_power);
        match identity.target {
            QuotientTarget::Main => main_numerator += scaled,
            QuotientTarget::Selector(selector_idx) => selector_buckets[selector_idx] += scaled,
        }
        identity_trace.push(TestIdentityTraceEntry {
            global_index: identity.meta.global_index,
            target: identity.target,
            value,
            y_power,
        });
    }

    TestLinearizationArtifacts {
        identity_trace,
        main_numerator,
        selector_buckets,
        quotient_expected_eval: -main_numerator,
    }
}

/// Interpret folded quotient bytecode into the same artifacts the verifier
/// uses.
fn eval_quotient_program_artifacts_for_test(
    bytes: &[u8],
    consts: &[U256],
    mem: &HashMap<u32, Fq>,
    y: Fq,
    selector_tail_exponents: &[usize],
) -> TestLinearizationArtifacts {
    let mut idx = 0usize;
    let mut identity_start = 0usize;
    let mut main_numerator = Fq::ZERO;
    let mut selector_buckets = vec![Fq::ZERO; selector_tail_exponents.len()];
    let mut identity_trace = Vec::new();

    while idx < bytes.len() {
        match bytes[idx] {
            Q_OP_FOLD_MAIN => {
                let value = eval_quotient_vm_for_test(&bytes[identity_start..idx], consts, mem);
                main_numerator = main_numerator * y + value;
                identity_trace.push(TestIdentityTraceEntry {
                    global_index: identity_trace.len(),
                    target: QuotientTarget::Main,
                    value,
                    y_power: 0,
                });
                idx += 1;
                identity_start = idx;
            }
            Q_OP_FOLD_SELECTOR => {
                let value = eval_quotient_vm_for_test(&bytes[identity_start..idx], consts, mem);
                let selector_idx = bytes[idx + 1] as usize;
                let gap = read_u16(bytes, idx + 2) as usize;
                main_numerator *= y;
                selector_buckets[selector_idx] =
                    selector_buckets[selector_idx] * fq_pow(y, gap) + value;
                identity_trace.push(TestIdentityTraceEntry {
                    global_index: identity_trace.len(),
                    target: QuotientTarget::Selector(selector_idx),
                    value,
                    y_power: 0,
                });
                idx += 4;
                identity_start = idx;
            }
            op => {
                let len = quotient_opcode_byte_len(op)
                    .unwrap_or_else(|| panic!("dynamic test opcode {op:#x} at byte {idx}"));
                idx += len;
            }
        }
    }

    assert_eq!(identity_start, bytes.len(), "program ended mid-identity");
    let total = identity_trace.len();
    for entry in &mut identity_trace {
        entry.y_power = total - 1 - entry.global_index;
    }
    for (bucket, tail) in selector_buckets.iter_mut().zip(selector_tail_exponents) {
        *bucket *= fq_pow(y, *tail);
    }

    TestLinearizationArtifacts {
        identity_trace,
        main_numerator,
        selector_buckets,
        quotient_expected_eval: -main_numerator,
    }
}

/// Evaluate the typed quotient expression tree for tests.
fn eval_quotient_expr_for_test(expr: &QuotientExpr, mem: &HashMap<u32, Fq>) -> Fq {
    match expr {
        QuotientExpr::Const(value) => fq_from_u256(*value),
        QuotientExpr::Mem(QuotientMem::Literal(ptr)) => mem[ptr],
        QuotientExpr::Mem(QuotientMem::Token(_))
        | QuotientExpr::Mem(QuotientMem::TokenOffset(_, _)) => {
            panic!("test expressions use literal memory only")
        }
        QuotientExpr::Add(lhs, rhs) => {
            eval_quotient_expr_for_test(lhs, mem) + eval_quotient_expr_for_test(rhs, mem)
        }
        QuotientExpr::Mul(lhs, rhs) => {
            eval_quotient_expr_for_test(lhs, mem) * eval_quotient_expr_for_test(rhs, mem)
        }
        QuotientExpr::Neg(inner) => -eval_quotient_expr_for_test(inner, mem),
    }
}

/// Minimal Rust interpreter for quotient VM opcodes used by regression tests.
fn eval_quotient_vm_for_test(bytes: &[u8], consts: &[U256], mem: &HashMap<u32, Fq>) -> Fq {
    let mut idx = 0usize;
    let mut stack: Vec<Fq> = Vec::new();

    while idx < bytes.len() {
        match bytes[idx] {
            Q_OP_PUSH_CONST => {
                let slot = read_u16(bytes, idx + 1) as usize;
                stack.push(fq_from_u256(consts[slot]));
                idx += 3;
            }
            Q_OP_PUSH_CONST_U8 => {
                let slot = bytes[idx + 1] as usize;
                stack.push(fq_from_u256(consts[slot]));
                idx += 2;
            }
            Q_OP_PUSH_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1) as u32;
                stack.push(mem[&ptr]);
                idx += 3;
            }
            Q_OP_PUSH_MEM_LITERAL => {
                let ptr = read_u32(bytes, idx + 1);
                stack.push(mem[&ptr]);
                idx += 5;
            }
            Q_OP_ADD => {
                let rhs = stack.pop().expect("rhs");
                let lhs = stack.pop().expect("lhs");
                stack.push(lhs + rhs);
                idx += 1;
            }
            Q_OP_MUL => {
                let rhs = stack.pop().expect("rhs");
                let lhs = stack.pop().expect("lhs");
                stack.push(lhs * rhs);
                idx += 1;
            }
            Q_OP_NEG => {
                let value = stack.pop().expect("value");
                stack.push(-value);
                idx += 1;
            }
            Q_OP_POW5 => {
                let value = stack.pop().expect("value");
                let value2 = value * value;
                stack.push(value * value2 * value2);
                idx += 1;
            }
            Q_OP_ADD_CONST_U8 => {
                let slot = bytes[idx + 1] as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc + fq_from_u256(consts[slot]));
                idx += 2;
            }
            Q_OP_MUL_CONST_U8 => {
                let slot = bytes[idx + 1] as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc * fq_from_u256(consts[slot]));
                idx += 2;
            }
            Q_OP_ADD_CONST => {
                let slot = read_u16(bytes, idx + 1) as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc + fq_from_u256(consts[slot]));
                idx += 3;
            }
            Q_OP_MUL_CONST => {
                let slot = read_u16(bytes, idx + 1) as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc * fq_from_u256(consts[slot]));
                idx += 3;
            }
            Q_OP_ADD_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1) as u32;
                let acc = stack.pop().expect("acc");
                stack.push(acc + mem[&ptr]);
                idx += 3;
            }
            Q_OP_MUL_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1) as u32;
                let acc = stack.pop().expect("acc");
                stack.push(acc * mem[&ptr]);
                idx += 3;
            }
            Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => {
                let lhs = read_u16(bytes, idx + 1) as u32;
                let rhs = read_u16(bytes, idx + 3) as u32;
                let slot = bytes[idx + 5] as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc + mem[&lhs] * mem[&rhs] * fq_from_u256(consts[slot]));
                idx += 6;
            }
            Q_OP_ADD_MUL_CONST_U8_MEM_U16 => {
                let ptr = read_u16(bytes, idx + 1) as u32;
                let slot = bytes[idx + 3] as usize;
                let acc = stack.pop().expect("acc");
                stack.push(acc + fq_from_u256(consts[slot]) * mem[&ptr]);
                idx += 4;
            }
            Q_OP_ADD_MUL_MEM_MEM => {
                let lhs = read_u16(bytes, idx + 1) as u32;
                let rhs = read_u16(bytes, idx + 3) as u32;
                let acc = stack.pop().expect("acc");
                stack.push(acc + mem[&lhs] * mem[&rhs]);
                idx += 5;
            }
            Q_OP_LIN7 => {
                let mut acc = Fq::ZERO;
                idx += 1;
                for _ in 0..7 {
                    let slot = bytes[idx] as usize;
                    let ptr = read_u16(bytes, idx + 1) as u32;
                    acc += fq_from_u256(consts[slot]) * mem[&ptr];
                    idx += 3;
                }
                stack.push(acc);
            }
            Q_OP_BILIN7_ROW => {
                let lhs = read_u16(bytes, idx + 1) as u32;
                let lhs_value = mem[&lhs];
                let mut acc = Fq::ZERO;
                idx += 3;
                for _ in 0..7 {
                    let slot = bytes[idx] as usize;
                    let rhs = read_u16(bytes, idx + 1) as u32;
                    acc += lhs_value * mem[&rhs] * fq_from_u256(consts[slot]);
                    idx += 3;
                }
                stack.push(acc);
            }
            Q_OP_BILIN7_PAIRWISE => {
                let lhs_base = read_u16(bytes, idx + 1) as u32;
                let rhs_base = read_u16(bytes, idx + 3) as u32;
                let coeff_idx = idx + 5;
                let mut acc = Fq::ZERO;
                for i in 0..7 {
                    let lhs = mem[&(lhs_base + i * 0x20)];
                    for j in 0..7 {
                        let rhs = mem[&(rhs_base + j * 0x20)];
                        let slot = bytes[coeff_idx + i as usize + j as usize] as usize;
                        acc += lhs * rhs * fq_from_u256(consts[slot]);
                    }
                }
                idx += 18;
                stack.push(acc);
            }
            Q_OP_MODARITH7 => {
                idx += 1;
                let flags = bytes[idx];
                idx += 1;
                let cond = if flags & 0x01 != 0 {
                    let ptr = read_u16(bytes, idx) as u32;
                    idx += 2;
                    Some(ptr)
                } else {
                    None
                };

                let mut acc = Fq::ZERO;
                if flags & 0x02 != 0 {
                    let slot = bytes[idx] as usize;
                    idx += 1;
                    acc += fq_from_u256(consts[slot]);
                }

                let lin_count = bytes[idx] as usize;
                let row_count = bytes[idx + 1] as usize;
                let pairwise_count = bytes[idx + 2] as usize;
                let mem_count = bytes[idx + 3] as usize;
                let product_count = bytes[idx + 4] as usize;
                idx += 5;

                for _ in 0..lin_count {
                    for _ in 0..7 {
                        let slot = bytes[idx] as usize;
                        let ptr = read_u16(bytes, idx + 1) as u32;
                        acc += fq_from_u256(consts[slot]) * mem[&ptr];
                        idx += 3;
                    }
                }
                for _ in 0..row_count {
                    let lhs = read_u16(bytes, idx) as u32;
                    let lhs_value = mem[&lhs];
                    idx += 2;
                    for _ in 0..7 {
                        let slot = bytes[idx] as usize;
                        let rhs = read_u16(bytes, idx + 1) as u32;
                        acc += lhs_value * mem[&rhs] * fq_from_u256(consts[slot]);
                        idx += 3;
                    }
                }
                for _ in 0..pairwise_count {
                    let lhs_base = read_u16(bytes, idx) as u32;
                    let rhs_base = read_u16(bytes, idx + 2) as u32;
                    idx += 4;
                    let coeff_idx = idx;
                    idx += 13;
                    for i in 0..7u32 {
                        let lhs = mem[&(lhs_base + i * WORD_BYTES as u32)];
                        for j in 0..7u32 {
                            let rhs = mem[&(rhs_base + j * WORD_BYTES as u32)];
                            let slot = bytes[coeff_idx + i as usize + j as usize] as usize;
                            acc += lhs * rhs * fq_from_u256(consts[slot]);
                        }
                    }
                }
                for _ in 0..mem_count {
                    let slot = bytes[idx] as usize;
                    let ptr = read_u16(bytes, idx + 1) as u32;
                    acc += fq_from_u256(consts[slot]) * mem[&ptr];
                    idx += 3;
                }
                for _ in 0..product_count {
                    let slot = bytes[idx] as usize;
                    let lhs = read_u16(bytes, idx + 1) as u32;
                    let rhs = read_u16(bytes, idx + 3) as u32;
                    acc += fq_from_u256(consts[slot]) * mem[&lhs] * mem[&rhs];
                    idx += 5;
                }

                if let Some(cond) = cond {
                    acc *= mem[&cond];
                }
                stack.push(acc);
            }
            op => panic!("unsupported test quotient VM op {op:#x} at byte {idx}"),
        }
    }

    assert_eq!(stack.len(), 1, "test VM should leave one result");
    stack.pop().unwrap()
}

/// Convert a canonical U256 test literal into Fr.
fn fq_from_u256(value: U256) -> Fq {
    let bytes = value.to_le_bytes::<32>();
    let repr = <Fq as PrimeField>::Repr::from(bytes);
    Option::<Fq>::from(Fq::from_repr(repr)).expect("canonical field element")
}

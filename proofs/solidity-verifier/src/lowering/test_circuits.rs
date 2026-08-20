// SPDX-License-Identifier: CC0-1.0
//! SRS-free test circuits shared by the lowering unit tests and the EVM
//! quotient frame differential.
//!
//! These live outside `lowering::tests` so `src/test.rs` (compiled under
//! `cfg(all(test, feature = "evm"))`) can reuse the same VM-exercising
//! fixture without duplicating it.

use ff::Field;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Constraints,
        Error as PlonkError, Expression, Selector, VerifyingKey,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

use super::config::{DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES, DEFAULT_QUOTIENT_NATIVE_GATES};

/// Number of advice columns backing one seven-limb foreign-field shape.
pub(crate) const QUOTIENT_VM_TEST_LIMBS: usize = 7;
/// Gate count chosen to exceed the inline prefix plus the native-gate budget,
/// so identities are left over for the compact VM.
pub(crate) const QUOTIENT_VM_TEST_GATES: usize =
    DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES + DEFAULT_QUOTIENT_NATIVE_GATES + 8;

#[derive(Clone, Debug)]
pub(crate) struct QuotientVmTestConfig {
    limbs: [Column<Advice>; QUOTIENT_VM_TEST_LIMBS],
    selector: Selector,
}

/// Circuit whose quotient identities are numerous enough to reach the VM.
///
/// `LoweringPlanTestCircuit` has a single gate, so its whole identity stream
/// fits in the inline prefix and the compact VM never runs. This circuit exists
/// so the fast test suite exercises the bytecode path — and therefore the
/// generator's own program certification — on a real `LoweringPlan`.
#[derive(Clone, Debug, Default)]
pub(crate) struct QuotientVmTestCircuit;

impl Circuit<Fq> for QuotientVmTestCircuit {
    type Config = QuotientVmTestConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let limbs: [Column<Advice>; QUOTIENT_VM_TEST_LIMBS] =
            core::array::from_fn(|_| meta.advice_column());
        let selector = meta.selector();
        // The generator only supports one identity-committed plus one
        // non-committed instance column, so mirror that shape here.
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();

        meta.create_gate("quotient vm instance balance", |meta| {
            let advice = meta.query_advice(limbs[0], Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());
            Constraints::without_selector(vec![advice + committed + public])
        });

        // Seven-limb linear forms: the shape the LIN7 recognizer is built for.
        // Distinct per-gate coefficients keep the gates from deduplicating.
        for gate in 0..QUOTIENT_VM_TEST_GATES {
            meta.create_gate("quotient vm limb form", move |meta| {
                let terms = limbs
                    .iter()
                    .enumerate()
                    .map(|(limb, column)| {
                        let coeff = Fq::from(((gate + 1) * 16 + limb + 1) as u64);
                        meta.query_advice(*column, Rotation::cur()) * Expression::Constant(coeff)
                    })
                    .reduce(|acc, term| acc + term)
                    .expect("limb count is nonzero");
                Constraints::without_selector(vec![terms])
            });
        }

        // One simple-selector gate so the selector fold path is covered too.
        meta.create_gate("quotient vm selector form", |meta| {
            let lhs = meta.query_advice(limbs[0], Rotation::cur());
            let rhs = meta.query_advice(limbs[1], Rotation::cur());
            Constraints::with_selector(selector, vec![("quotient vm selector form", lhs - rhs)])
        });

        QuotientVmTestConfig { limbs, selector }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        layouter.assign_region(
            || "quotient vm row",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                for column in config.limbs {
                    region.assign_advice(|| "limb", column, 0, || Value::known(Fq::ZERO))?;
                }
                Ok(())
            },
        )
    }
}

/// Generate parameters and VK for the VM-exercising lowering-plan tests.
pub(crate) fn quotient_vm_test_vk() -> (
    ParamsKZG<Bls12>,
    VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
) {
    let mut rng = ChaCha8Rng::seed_from_u64(11);
    let params = ParamsKZG::<Bls12>::unsafe_setup(6, &mut rng);
    let circuit = QuotientVmTestCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 6)
        .expect("quotient VM test circuit VK should build");
    (params, vk)
}

/// Selector gates beyond what the inline prefix and native-gate budget can
/// absorb, so at least two selector identities must be interpreted by the
/// compact VM (`FOLD_SELECTOR` in bytecode) regardless of which gates the
/// knapsack picks.
pub(crate) const QUOTIENT_SELECTOR_FOLD_TEST_GATES: usize =
    DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES + DEFAULT_QUOTIENT_NATIVE_GATES + 2;

#[derive(Clone, Debug)]
pub(crate) struct QuotientSelectorFoldTestConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    selectors: [Selector; 2],
}

/// Circuit whose selector identities must overflow into the compact VM.
///
/// Every gate beyond the mandatory instance balance targets one of two
/// simple-selector buckets, alternating, so the interpreted stream is
/// guaranteed to contain `FOLD_SELECTOR` opcodes with intra-bucket gaps — the
/// operand class the frame differential's negative controls mutate.
#[derive(Clone, Debug, Default)]
pub(crate) struct QuotientSelectorFoldTestCircuit;

impl Circuit<Fq> for QuotientSelectorFoldTestCircuit {
    type Config = QuotientSelectorFoldTestConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let selectors = [meta.selector(), meta.selector()];
        // The generator only supports one identity-committed plus one
        // non-committed instance column, so mirror that shape here.
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();

        meta.create_gate("selector fold instance balance", |meta| {
            let advice = meta.query_advice(a, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());
            Constraints::without_selector(vec![advice + committed + public])
        });

        // Distinct per-gate coefficients keep the gates from deduplicating.
        for gate in 0..QUOTIENT_SELECTOR_FOLD_TEST_GATES {
            let selector = selectors[gate % 2];
            meta.create_gate("selector fold form", move |meta| {
                let lhs = meta.query_advice(a, Rotation::cur());
                let rhs = meta.query_advice(b, Rotation::cur());
                let scaled = (lhs - rhs) * Expression::Constant(Fq::from((gate + 3) as u64));
                Constraints::with_selector(selector, vec![("selector fold form", scaled)])
            });
        }

        QuotientSelectorFoldTestConfig { a, b, selectors }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        layouter.assign_region(
            || "selector fold row",
            |mut region| {
                for selector in config.selectors {
                    selector.enable(&mut region, 0)?;
                }
                region.assign_advice(|| "a", config.a, 0, || Value::known(Fq::ZERO))?;
                region.assign_advice(|| "b", config.b, 0, || Value::known(Fq::ZERO))?;
                Ok(())
            },
        )
    }
}

/// Generate parameters and VK for the selector-fold pigeonhole circuit.
pub(crate) fn quotient_selector_fold_test_vk() -> (
    ParamsKZG<Bls12>,
    VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
) {
    let mut rng = ChaCha8Rng::seed_from_u64(13);
    let params = ParamsKZG::<Bls12>::unsafe_setup(6, &mut rng);
    let circuit = QuotientSelectorFoldTestCircuit;
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, 6)
        .expect("selector fold test circuit VK should build");
    (params, vk)
}

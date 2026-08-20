// SPDX-License-Identifier: CC0-1.0
//! Curated supported-shape circuit corpus shared by the EVM differentials and
//! the always-on corpus certification tests.
//!
//! This module deliberately compiles WITHOUT the `evm` feature so its tier-1
//! tests run under plain `cargo test`: every case must MockProver-prove
//! (guarding the proving-tier corpus e2e), build a certified lowering plan
//! (which runs `validate_quotient_mem_ptrs`, `certify_quotient_program`, and
//! the dual-build certification), satisfy its per-case coverage expectation,
//! and render cleanly, before any EVM-side differential consumes it.

use std::collections::BTreeSet;

use ff::Field;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Fixed,
        SecondPhase, Selector,
    },
    poly::Rotation,
};
use rand_chacha::ChaCha8Rng;

use crate::lowering::{
    config::{DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES, DEFAULT_QUOTIENT_NATIVE_GATES},
    plan::LoweringPlan,
    quotient_numerator::vm::{self as vm, QuotientExecutionKind},
    VerifierBuildInputs,
};

/// Scalar field used by the shape-fuzz corpus.
type F = Fq;
/// KZG parameters type used by shape-fuzz keygen.
pub(crate) type ShapeFuzzParams = midnight_proofs::poly::kzg::params::ParamsKZG<Bls12>;

/// Circuit domain size used by the generated-shape fuzzers.
pub(crate) const SHAPE_FUZZ_K: u32 = 5;

/// Identities the inline prefix plus the native-gate knapsack can absorb.
///
/// Pigeonhole-sized gate classes add this many gates on top of the requested
/// count so the requested number provably lands on the Interpreted surface no
/// matter which gates the (intentionally divergent) knapsack picks — and the
/// sizing survives budget changes because it is written in terms of the
/// budgets themselves.
const CORPUS_ABSORPTION_BUDGET: usize =
    DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES + DEFAULT_QUOTIENT_NATIVE_GATES;

/// Structural axes of one generated supported-shape circuit.
///
/// The first block is the legacy axis set; seed bits 0–6 of
/// [`generated_shape_fuzz_spec`] keep their exact historical meaning. The
/// second block holds the additive axes: every one defaults to off, is
/// provable by construction (enforced by the tier-1 MockProver guard), and
/// only appends columns/gates after the legacy shape, so legacy specs render
/// byte-identically.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct ShapeFuzzSpec {
    pub(crate) next_rotation: bool,
    pub(crate) second_phase: bool,
    pub(crate) permutation: bool,
    pub(crate) lookup: bool,
    pub(crate) additive_selector: bool,
    pub(crate) complex_selector: bool,
    pub(crate) fixed_scale: bool,
    pub(crate) tag: u64,
    /// Multiply an extra balance constraint by `a^boost`, raising
    /// `cs.degree()` (and with it `permutation_chunk_len` and the lookup
    /// `chunk_by_degree` split) without changing satisfiability.
    pub(crate) gate_degree_boost: u8,
    /// Add six more equality-enabled advice columns (nine total with
    /// `a`/`b`/`out`), forcing multiple permutation sets: continuity
    /// constraints plus a multi-chunk delta walk.
    pub(crate) wide_permutation: bool,
    /// Extra single-expression parallel inputs added to the base lookup
    /// argument (ignored unless `lookup` is on), driving multi-input helper
    /// chunks through the staged prefix/suffix tables and the `k == 1` arm.
    pub(crate) lookup_parallel: u8,
    /// Additional independent lookup arguments, each with its own fixed
    /// table and no selector.
    pub(crate) extra_lookup_args: u8,
    /// Seven-limb linear gates (the LIN7 recognizer shape), pigeonhole-sized:
    /// the circuit adds `CORPUS_ABSORPTION_BUDGET + limb7_gates` of them.
    pub(crate) limb7_gates: u8,
    /// Seven-limb row-bilinear gates (`b * Σ coeff_i * limb_i`),
    /// pigeonhole-sized like `limb7_gates`. At identity level the lowering
    /// routes this shape through the MODARITH7 superinstruction (a
    /// conditionally gated mixed affine form), which subsumes bare
    /// BILIN7_ROW; the standalone BILIN7_* opcodes stay covered by the
    /// direct emitter unit tests and the reference interpreter.
    pub(crate) limb7_bilinear_gates: u8,
    /// Simple-selector gates alternating between two buckets,
    /// pigeonhole-sized so `FOLD_SELECTOR` provably reaches the bytecode.
    pub(crate) selector_gate_count: u8,
    /// Extra Main-target product-of-sums gates (behind a shared complex
    /// selector), interleaved between the selector gates to widen
    /// intra-bucket gaps. Pigeonhole-sized like the other classes so the
    /// generic `MUL` opcode provably reaches the bytecode.
    pub(crate) extra_main_gates: u8,
    /// Fifth-power gates (the POW5 recognizer shape), pigeonhole-sized with
    /// one guaranteed-interpreted gate.
    pub(crate) pow5_gate: bool,
    /// A `Rotation::prev` constraint behind a dedicated complex selector
    /// enabled on row 1.
    pub(crate) prev_rotation: bool,
}

/// One curated corpus entry.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ShapeFuzzCase {
    pub(crate) name: &'static str,
    pub(crate) k: u32,
    pub(crate) spec: ShapeFuzzSpec,
    pub(crate) seed: u64,
}

#[derive(Clone, Debug)]
pub(crate) struct ShapeFuzzConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    out: Column<Advice>,
    phase2: Option<Column<Advice>>,
    fixed_scale: Option<Column<Fixed>>,
    lookup_table: Option<Column<Fixed>>,
    selector: Selector,
    wide_columns: Vec<Column<Advice>>,
    limb_columns: Vec<Column<Fixed>>,
    bilinear_lhs: Option<Column<Fixed>>,
    parallel_columns: Vec<Column<Advice>>,
    extra_tables: Vec<Column<Fixed>>,
    bucket_selectors: Vec<Selector>,
    extra_main_selector: Option<Selector>,
    prev_selector: Option<Selector>,
    pow5_columns: Option<(Column<Fixed>, Column<Fixed>)>,
}

#[derive(Clone, Debug)]
pub(crate) struct ShapeFuzzCircuit {
    spec: ShapeFuzzSpec,
    a: F,
    b: F,
}

/// Fifth power over Fr, shared by witness assignment.
fn pow5(value: F) -> F {
    let squared = value * value;
    value * squared * squared
}

impl ShapeFuzzCircuit {
    /// Deterministically construct a shape-fuzz witness.
    pub(crate) fn new(spec: ShapeFuzzSpec, seed: u64) -> Self {
        let a = F::from(seed.wrapping_mul(17).wrapping_add(5));
        let b = F::from(seed.wrapping_mul(29).wrapping_add(11));
        Self { spec, a, b }
    }

    /// Advice output constrained by the synthetic circuit.
    fn out(&self) -> F {
        self.a + self.b + F::from(self.spec.tag + 19)
    }

    /// Public input derived from the output and advice values.
    pub(crate) fn public_instance(&self) -> F {
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

        if spec.permutation || spec.wide_permutation {
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

        let mut parallel_columns = Vec::new();
        if let Some(table) = lookup_table {
            if spec.lookup_parallel == 0 {
                meta.lookup_any("shape-fuzz lookup", Some(selector), |meta| {
                    vec![(
                        meta.query_advice(a, Rotation::cur()),
                        meta.query_fixed(table, Rotation::cur()),
                    )]
                });
            } else {
                for _ in 0..spec.lookup_parallel {
                    parallel_columns.push(meta.advice_column());
                }
                let parallel = parallel_columns.clone();
                meta.batch_lookup_any("shape-fuzz lookup", Some(selector), |meta| {
                    let mut inputs = vec![meta.query_advice(a, Rotation::cur())];
                    inputs.extend(
                        parallel.iter().map(|column| meta.query_advice(*column, Rotation::cur())),
                    );
                    vec![(inputs, meta.query_fixed(table, Rotation::cur()))]
                });
            }
        }

        // --------------------------------------------------------------
        // Additive axes. Everything below appends columns and gates after
        // the legacy shape, so specs with these axes off configure the
        // exact constraint system they always did.
        // --------------------------------------------------------------

        if spec.gate_degree_boost > 0 {
            meta.create_gate("shape-fuzz degree boost", move |meta| {
                let a_cur = meta.query_advice(a, Rotation::cur());
                let b_cur = meta.query_advice(b, Rotation::cur());
                let out_cur = meta.query_advice(out, Rotation::cur());
                let committed = meta.query_instance(committed_instance, Rotation::cur());
                let public = meta.query_instance(public_instance, Rotation::cur());
                let mut balance = a_cur.clone() + b_cur + public + committed - out_cur;
                if let Some(scale) = fixed_scale {
                    balance = meta.query_fixed(scale, Rotation::cur()) * balance;
                }
                // The balance factor is zero on every selector-active row, so
                // multiplying by `a^boost` raises the structural degree
                // without changing satisfiability.
                let mut boosted = balance;
                for _ in 0..spec.gate_degree_boost {
                    boosted = boosted * a_cur.clone();
                }
                Constraints::with_selector(selector, vec![("degree boost", boosted)])
            });
        }

        let mut wide_columns = Vec::new();
        if spec.wide_permutation {
            for _ in 0..6 {
                let column = meta.advice_column();
                meta.enable_equality(column);
                wide_columns.push(column);
            }
        }

        // Ungated (`without_selector`) shapes must vanish on the blinding
        // rows too, so they are built over FIXED columns: fixed cells are
        // zero-filled instead of blinded, the constraints hold identically,
        // and the fixed queries still lower to memory-backed proof-eval
        // words that hit the LIN7/MODARITH7/POW5 recognizers.
        let mut limb_columns = Vec::new();
        let mut bilinear_lhs = None;
        if spec.limb7_gates > 0 || spec.limb7_bilinear_gates > 0 {
            let limbs: [Column<Fixed>; 7] = core::array::from_fn(|_| meta.fixed_column());
            limb_columns = limbs.to_vec();

            let lin_gates = if spec.limb7_gates > 0 {
                CORPUS_ABSORPTION_BUDGET + spec.limb7_gates as usize
            } else {
                0
            };
            for gate in 0..lin_gates {
                let tag = spec.tag;
                meta.create_gate("shape-fuzz limb form", move |meta| {
                    let terms = limbs
                        .iter()
                        .enumerate()
                        .map(|(limb, column)| {
                            let coeff = F::from(((gate + 2) * 32 + limb + 1) as u64 + tag);
                            meta.query_fixed(*column, Rotation::cur()) * Expression::Constant(coeff)
                        })
                        .reduce(|acc, term| acc + term)
                        .expect("limb count is nonzero");
                    Constraints::without_selector(vec![terms])
                });
            }

            let bilin_gates = if spec.limb7_bilinear_gates > 0 {
                bilinear_lhs = Some(meta.fixed_column());
                CORPUS_ABSORPTION_BUDGET + spec.limb7_bilinear_gates as usize
            } else {
                0
            };
            for gate in 0..bilin_gates {
                let tag = spec.tag;
                let lhs_column = bilinear_lhs.expect("allocated when bilinear gates exist");
                meta.create_gate("shape-fuzz bilinear limb form", move |meta| {
                    let row = limbs
                        .iter()
                        .enumerate()
                        .map(|(limb, column)| {
                            let coeff = F::from(((gate + 3) * 64 + limb + 1) as u64 + tag);
                            meta.query_fixed(*column, Rotation::cur()) * Expression::Constant(coeff)
                        })
                        .reduce(|acc, term| acc + term)
                        .expect("limb count is nonzero");
                    let lhs = meta.query_fixed(lhs_column, Rotation::cur());
                    Constraints::without_selector(vec![lhs * row])
                });
            }
        }

        let pow5_columns = spec.pow5_gate.then(|| (meta.fixed_column(), meta.fixed_column()));
        if let Some((pow5_base, pow5_out)) = pow5_columns {
            for gate in 0..CORPUS_ABSORPTION_BUDGET + 1 {
                meta.create_gate("shape-fuzz pow5 form", move |meta| {
                    let base = meta.query_fixed(pow5_base, Rotation::cur());
                    let fifth = base.clone() * base.clone() * base.clone() * base.clone() * base;
                    let expected = meta.query_fixed(pow5_out, Rotation::cur());
                    let constraint =
                        (fifth - expected) * Expression::Constant(F::from((gate + 2) as u64));
                    Constraints::without_selector(vec![("pow5 form", constraint)])
                });
            }
        }

        let mut bucket_selectors = Vec::new();
        let selector_gates = if spec.selector_gate_count > 0 {
            bucket_selectors = vec![meta.selector(), meta.selector()];
            CORPUS_ABSORPTION_BUDGET + spec.selector_gate_count as usize
        } else {
            0
        };
        let extra_main_gates = if spec.extra_main_gates > 0 {
            CORPUS_ABSORPTION_BUDGET + spec.extra_main_gates as usize
        } else {
            0
        };
        let extra_main_selector = (extra_main_gates > 0).then(|| meta.complex_selector());
        // Interleave the two classes so identities of one selector bucket are
        // separated by other identities, producing intra-bucket fold gaps
        // greater than one.
        for position in 0..selector_gates.max(extra_main_gates) {
            if position < selector_gates {
                let bucket = bucket_selectors[position % 2];
                let tag = spec.tag;
                meta.create_gate("shape-fuzz selector bucket form", move |meta| {
                    let a_cur = meta.query_advice(a, Rotation::cur());
                    let b_cur = meta.query_advice(b, Rotation::cur());
                    let out_cur = meta.query_advice(out, Rotation::cur());
                    let scaled =
                        (out_cur - a_cur - b_cur - Expression::Constant(F::from(tag + 19)))
                            * Expression::Constant(F::from((position + 2) as u64));
                    Constraints::with_selector(bucket, vec![("selector bucket form", scaled)])
                });
            }
            if position < extra_main_gates {
                let extra = extra_main_selector.expect("allocated when extra_main_gates > 0");
                let tag = spec.tag;
                meta.create_gate("shape-fuzz extra main form", move |meta| {
                    let a_cur = meta.query_advice(a, Rotation::cur());
                    let b_cur = meta.query_advice(b, Rotation::cur());
                    let out_cur = meta.query_advice(out, Rotation::cur());
                    // Product of two non-leaf sums: the second factor is zero
                    // on every selector-active row, and the shape reaches the
                    // generic `MUL` opcode (no fused/limb recognizer matches
                    // a product of sums).
                    let vanishing = out_cur
                        - a_cur.clone()
                        - b_cur.clone()
                        - Expression::Constant(F::from(tag + 19));
                    let scaled = ((a_cur + b_cur) * vanishing)
                        * Expression::Constant(F::from((position + 100) as u64));
                    Constraints::with_selector(extra, vec![("extra main form", scaled)])
                });
            }
        }

        let prev_selector = spec.prev_rotation.then(|| meta.complex_selector());
        if let Some(prev_selector) = prev_selector {
            let tag = spec.tag;
            meta.create_gate("shape-fuzz prev rotation", move |meta| {
                let a_prev = meta.query_advice(a, Rotation::prev());
                let a_cur = meta.query_advice(a, Rotation::cur());
                // Enabled on row 1, where a(0) = a and a(1) = a + tag + 7.
                let constraint = a_prev - a_cur + Expression::Constant(F::from(tag + 7));
                Constraints::with_selector(prev_selector, vec![("prev rotation", constraint)])
            });
        }

        let mut extra_tables = Vec::new();
        for arg in 0..spec.extra_lookup_args {
            let extra_table = meta.fixed_column();
            extra_tables.push(extra_table);
            meta.lookup_any(format!("shape-fuzz extra lookup {arg}"), None, |meta| {
                vec![(
                    meta.query_advice(b, Rotation::cur()),
                    meta.query_fixed(extra_table, Rotation::cur()),
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
            wide_columns,
            limb_columns,
            bilinear_lhs,
            parallel_columns,
            extra_tables,
            bucket_selectors,
            extra_main_selector,
            prev_selector,
            pow5_columns,
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

                if self.spec.next_rotation || self.spec.prev_rotation {
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

                // --- Additive axes ---

                for (idx, column) in config.wide_columns.iter().enumerate() {
                    region.assign_advice(
                        || "wide equality",
                        *column,
                        0,
                        || Value::known(F::from(idx as u64 + 31)),
                    )?;
                }
                if !config.wide_columns.is_empty() {
                    let copied = region.assign_advice(
                        || "wide source",
                        config.wide_columns[0],
                        4,
                        || Value::known(self.b),
                    )?;
                    copied.copy_advice(|| "wide target", &mut region, config.wide_columns[1], 5)?;
                }

                for column in &config.limb_columns {
                    region.assign_fixed(|| "limb", *column, 0, || Value::known(F::ZERO))?;
                }
                if let Some(column) = config.bilinear_lhs {
                    region.assign_fixed(
                        || "bilinear lhs",
                        column,
                        0,
                        || Value::known(F::from(self.spec.tag + 41)),
                    )?;
                }

                for column in &config.parallel_columns {
                    region.assign_advice(
                        || "parallel input",
                        *column,
                        0,
                        || Value::known(self.a),
                    )?;
                }

                for column in &config.extra_tables {
                    region.assign_fixed(
                        || "extra lookup table",
                        *column,
                        0,
                        || Value::known(self.b),
                    )?;
                }

                if let Some((base, out)) = config.pow5_columns {
                    let base_value = F::from(self.spec.tag + 29);
                    region.assign_fixed(|| "pow5 base", base, 0, || Value::known(base_value))?;
                    region.assign_fixed(
                        || "pow5 out",
                        out,
                        0,
                        || Value::known(pow5(base_value)),
                    )?;
                }

                for bucket in &config.bucket_selectors {
                    bucket.enable(&mut region, 0)?;
                }
                if let Some(extra) = config.extra_main_selector {
                    extra.enable(&mut region, 0)?;
                }
                if let Some(prev) = config.prev_selector {
                    prev.enable(&mut region, 1)?;
                }

                Ok(())
            },
        )
    }
}

/// The curated corpus: the seven legacy cases (unchanged) plus the additive
/// coverage cases. Select cases by NAME, never by index.
pub(crate) fn curated_cases() -> Vec<ShapeFuzzCase> {
    vec![
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
        // --- Additive coverage cases ---
        ShapeFuzzCase {
            name: "degree-4 boundary two-set permutation",
            k: 5,
            seed: 808,
            spec: ShapeFuzzSpec {
                permutation: true,
                gate_degree_boost: 2,
                tag: 8,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "degree-6 wide-permutation delta walk",
            k: 5,
            seed: 909,
            spec: ShapeFuzzSpec {
                permutation: true,
                wide_permutation: true,
                gate_degree_boost: 4,
                tag: 9,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "parallel-lookup chunk split",
            k: 5,
            seed: 1010,
            spec: ShapeFuzzSpec {
                lookup: true,
                lookup_parallel: 4,
                tag: 10,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "two lookup arguments",
            k: 5,
            seed: 1111,
            spec: ShapeFuzzSpec {
                lookup: true,
                extra_lookup_args: 1,
                tag: 11,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "trash tail without lookups",
            k: 5,
            seed: 1212,
            spec: ShapeFuzzSpec {
                additive_selector: true,
                permutation: true,
                prev_rotation: true,
                tag: 12,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "seven-limb foreign-field vm overflow",
            k: 6,
            seed: 1313,
            spec: ShapeFuzzSpec {
                limb7_gates: 2,
                limb7_bilinear_gates: 2,
                tag: 13,
                ..ShapeFuzzSpec::default()
            },
        },
        ShapeFuzzCase {
            name: "selector bucket gaps interleaved pow5",
            k: 5,
            seed: 1414,
            spec: ShapeFuzzSpec {
                selector_gate_count: 2,
                extra_main_gates: 2,
                pow5_gate: true,
                tag: 14,
                ..ShapeFuzzSpec::default()
            },
        },
    ]
}

/// Generate a random-ish supported circuit shape from a fuzz seed.
///
/// Bits 0–6 keep their exact historical meaning; the additive axes live on
/// bits 7+ and are all safe by construction (provable, budget-pigeonholed).
pub(crate) fn generated_shape_fuzz_spec(seed: u64) -> ShapeFuzzSpec {
    ShapeFuzzSpec {
        next_rotation: seed & 0x01 != 0,
        second_phase: seed & 0x02 != 0,
        permutation: seed & 0x04 != 0,
        lookup: seed & 0x08 != 0,
        additive_selector: seed & 0x10 != 0,
        complex_selector: seed & 0x20 != 0,
        fixed_scale: seed & 0x40 != 0,
        gate_degree_boost: ((seed >> 7) & 0x03) as u8,
        wide_permutation: seed & 0x200 != 0,
        lookup_parallel: ((seed >> 10) & 0x03) as u8,
        extra_lookup_args: ((seed >> 12) & 0x01) as u8,
        limb7_gates: ((seed >> 13) & 0x01) as u8,
        limb7_bilinear_gates: ((seed >> 14) & 0x01) as u8,
        selector_gate_count: ((seed >> 15) & 0x03) as u8,
        extra_main_gates: ((seed >> 17) & 0x03) as u8,
        pow5_gate: seed & 0x8_0000 != 0,
        prev_rotation: seed & 0x10_0000 != 0,
        tag: 100 + seed.rotate_left(17) % 10_000,
    }
}

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
pub(crate) fn shape_fuzz_params(
    shapes: &[(ShapeFuzzSpec, u32)],
    rng: &mut ChaCha8Rng,
) -> ShapeFuzzParams {
    let (_, lagrange_k) = shapes.first().copied().expect("at least one shape");
    assert!(
        shapes.iter().all(|(_, k)| *k == lagrange_k),
        "one parameter set can only serve shapes that share a circuit domain size"
    );

    #[cfg(not(feature = "outer-single-h-commitment"))]
    {
        ShapeFuzzParams::unsafe_setup(lagrange_k, rng)
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
        let mut params = ShapeFuzzParams::unsafe_setup(extended_k, rng);
        // Keep the monomial basis extended; shrink only the Lagrange basis back
        // to the circuit domain so commitments stay at 2^k.
        params.downsize_lagrange(lagrange_k);
        params
    }
}

// ---------------------------------------------------------------------
// Coverage machinery.
// ---------------------------------------------------------------------

/// Execution surfaces reached by one case.
///
/// Mirror of `QuotientExecutionKind` that erases the `NativeIdentity` payload
/// and is `Ord`, so coverage assertions can collect surfaces in a set.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum SurfaceKind {
    Inline,
    Interpreted,
    NativePermutation,
    NativeLookup,
    NativeIdentity,
    StructuredTail,
}

impl SurfaceKind {
    /// Every execution surface the generated evaluator can fold through.
    pub(crate) const ALL: [SurfaceKind; 6] = [
        SurfaceKind::Inline,
        SurfaceKind::Interpreted,
        SurfaceKind::NativePermutation,
        SurfaceKind::NativeLookup,
        SurfaceKind::NativeIdentity,
        SurfaceKind::StructuredTail,
    ];

    /// Collapse the payload-carrying execution kind into the mirror enum.
    pub(crate) fn of(kind: QuotientExecutionKind) -> Self {
        match kind {
            QuotientExecutionKind::Inline => SurfaceKind::Inline,
            QuotientExecutionKind::Interpreted => SurfaceKind::Interpreted,
            QuotientExecutionKind::NativePermutation => SurfaceKind::NativePermutation,
            QuotientExecutionKind::NativeLookup => SurfaceKind::NativeLookup,
            QuotientExecutionKind::NativeIdentity { .. } => SurfaceKind::NativeIdentity,
            QuotientExecutionKind::StructuredTail => SurfaceKind::StructuredTail,
        }
    }
}

/// Emission arm one lookup helper chunk dispatches to, mirroring
/// `structured_lookup_loop_block`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum LookupChunkArm {
    /// `k == 1`: direct `h * (f + beta) - 1` identity.
    Single,
    /// `k >= 3` with a shared prefix and adjacent tails.
    SharedPrefix,
    /// `k >= 2` generic staged prefix/suffix product tables.
    Staged,
}

/// What one curated case must structurally provide.
///
/// Growing an expectation is encouraged; shrinking one is a review event —
/// it means a lowering change silently removed coverage the corpus was
/// counted on to provide.
pub(crate) struct CoverageExpectation {
    /// Exact `cs.degree()` when the case exists to pin a degree boundary.
    pub(crate) cs_degree: Option<usize>,
    /// Exact number of permutation z-polynomials, when pinned.
    pub(crate) permutation_sets: Option<usize>,
    /// Per-lookup-argument helper-chunk sizes (`k` vectors), exact.
    pub(crate) lookup_chunk_lens: &'static [&'static [usize]],
    /// Minimum number of trash identities.
    pub(crate) min_trash: usize,
    /// Execution surfaces this case must fold through.
    pub(crate) required_surfaces: &'static [SurfaceKind],
    /// Opcodes that must appear in the finalized bytecode.
    pub(crate) required_ops: &'static [u8],
    /// Rotations that must appear in gate queries.
    pub(crate) required_rotations: &'static [i32],
    /// Minimum simple-selector buckets.
    pub(crate) min_selector_buckets: usize,
    /// Minimum intra-bucket selector fold gap.
    pub(crate) min_selector_gap: usize,
    /// Minimum identities executed by the compact VM.
    pub(crate) min_interpreted: usize,
}

/// Per-case structural expectations, keyed by case name.
pub(crate) fn coverage_expectation(name: &str) -> CoverageExpectation {
    use SurfaceKind::*;
    let default = CoverageExpectation {
        cs_degree: None,
        permutation_sets: None,
        lookup_chunk_lens: &[],
        min_trash: 0,
        required_surfaces: &[Inline],
        required_ops: &[],
        required_rotations: &[0],
        min_selector_buckets: 0,
        min_selector_gap: 0,
        min_interpreted: 0,
    };
    match name {
        "simple-selector current-row fixed-scale" => CoverageExpectation {
            min_selector_buckets: 1,
            ..default
        },
        "next-rotation permutation" => CoverageExpectation {
            required_surfaces: &[Inline, NativePermutation],
            required_rotations: &[0, 1],
            ..default
        },
        "second-phase lookup" => CoverageExpectation {
            lookup_chunk_lens: &[&[1]],
            required_surfaces: &[Inline, NativeLookup],
            ..default
        },
        // `with_additive_selector` routes every constraint into the trash
        // argument, so additive cases have no gate identities at all — the
        // whole y-batch lives on the native/structured surfaces.
        "trash-additive selector with lookup" => CoverageExpectation {
            lookup_chunk_lens: &[&[1]],
            min_trash: 1,
            required_surfaces: &[NativeLookup, StructuredTail],
            required_rotations: &[0, 1],
            ..default
        },
        "complex-selector second-phase permutation" => CoverageExpectation {
            required_surfaces: &[Inline, NativePermutation],
            ..default
        },
        "additive-selector phase2 permutation" => CoverageExpectation {
            min_trash: 1,
            required_surfaces: &[NativePermutation, StructuredTail],
            ..default
        },
        // "Full mixed" uses a complex (not additive) selector, so it has no
        // trash argument; the trash surfaces are covered by the additive
        // cases.
        "full mixed lookup permutation shape" => CoverageExpectation {
            lookup_chunk_lens: &[&[1]],
            required_surfaces: &[Inline, NativePermutation, NativeLookup],
            required_rotations: &[0, 1],
            ..default
        },
        "degree-4 boundary two-set permutation" => CoverageExpectation {
            cs_degree: Some(4),
            permutation_sets: Some(2),
            required_surfaces: &[Inline, NativePermutation],
            min_selector_buckets: 1,
            ..default
        },
        "degree-6 wide-permutation delta walk" => CoverageExpectation {
            cs_degree: Some(6),
            permutation_sets: Some(3),
            required_surfaces: &[Inline, NativePermutation],
            min_selector_buckets: 1,
            ..default
        },
        "parallel-lookup chunk split" => CoverageExpectation {
            cs_degree: Some(5),
            lookup_chunk_lens: &[&[4, 1]],
            required_surfaces: &[Inline, NativeLookup],
            ..default
        },
        "two lookup arguments" => CoverageExpectation {
            lookup_chunk_lens: &[&[1], &[1]],
            required_surfaces: &[Inline, NativeLookup],
            ..default
        },
        "trash tail without lookups" => CoverageExpectation {
            min_trash: 1,
            required_surfaces: &[Inline, NativePermutation, StructuredTail],
            required_rotations: &[-1, 0],
            ..default
        },
        // Row-bilinear limb forms lower through the MODARITH7
        // superinstruction at identity level (it subsumes bare BILIN7_ROW);
        // the standalone BILIN7_* opcodes stay covered by the direct emitter
        // unit tests and the reference interpreter. NativeIdentity is
        // deliberately NOT required here: which gates go native is the
        // knapsack's intentionally divergent choice, asserted only at
        // corpus-union level.
        "seven-limb foreign-field vm overflow" => CoverageExpectation {
            required_surfaces: &[Inline, Interpreted],
            required_ops: &[vm::Q_OP_LIN7, vm::Q_OP_MODARITH7, vm::Q_OP_FOLD_MAIN],
            min_interpreted: 4,
            ..default
        },
        "selector bucket gaps interleaved pow5" => CoverageExpectation {
            required_surfaces: &[Inline, Interpreted],
            required_ops: &[vm::Q_OP_FOLD_SELECTOR, vm::Q_OP_POW5, vm::Q_OP_MUL],
            min_selector_buckets: 3,
            min_selector_gap: 2,
            min_interpreted: 3,
            ..default
        },
        other => panic!("no coverage expectation registered for corpus case `{other}`"),
    }
}

/// Opcode floor the corpus union must keep reaching. Growing this list is
/// encouraged; shrinking it is a review event. Deliberately NOT the full
/// `QUOTIENT_VM_SPEC` table: run-compaction and wide-pointer opcodes may be
/// unreachable at the corpus's small domain sizes, and the standalone
/// BILIN7_* opcodes are subsumed by MODARITH7 at identity level (they stay
/// covered by the direct emitter unit tests and the reference interpreter).
pub(crate) const REQUIRED_CORPUS_OPS: &[u8] = &[
    vm::Q_OP_PUSH_CONST_U8,
    vm::Q_OP_PUSH_MEM_U16,
    vm::Q_OP_ADD,
    vm::Q_OP_MUL,
    vm::Q_OP_NEG,
    vm::Q_OP_MUL_CONST_U8,
    vm::Q_OP_ADD_MEM_U16,
    vm::Q_OP_FOLD_MAIN,
    vm::Q_OP_FOLD_SELECTOR,
    vm::Q_OP_NATIVE_PERMUTATION,
    vm::Q_OP_NATIVE_LOOKUP,
    vm::Q_OP_NATIVE_IDENTITY,
    vm::Q_OP_LIN7,
    vm::Q_OP_MODARITH7,
    vm::Q_OP_POW5,
];

/// Rotations queried by any gate polynomial, trash constraint, or lookup
/// expression. Trashcans matter here: `with_additive_selector` moves every
/// constraint out of the gate list, so a gates-only scan would miss the
/// rotations of additive-selector shapes entirely.
fn query_rotations(cs: &ConstraintSystem<F>) -> BTreeSet<i32> {
    fn collect(expr: &Expression<F>, out: &mut BTreeSet<i32>) {
        match expr {
            Expression::Advice(query) => {
                out.insert(query.rotation().0);
            }
            Expression::Fixed(query) => {
                out.insert(query.rotation().0);
            }
            Expression::Instance(query) => {
                out.insert(query.rotation().0);
            }
            Expression::Negated(inner) | Expression::Scaled(inner, _) => collect(inner, out),
            Expression::Sum(lhs, rhs) | Expression::Product(lhs, rhs) => {
                collect(lhs, out);
                collect(rhs, out);
            }
            Expression::Constant(_) | Expression::Selector(_) | Expression::Challenge(_) => {}
        }
    }

    let mut rotations = BTreeSet::new();
    for gate in cs.gates() {
        for poly in gate.polynomials() {
            collect(poly, &mut rotations);
        }
    }
    for trash in cs.trashcans() {
        collect(trash.selector(), &mut rotations);
        for expr in trash.constraint_expressions() {
            collect(expr, &mut rotations);
        }
    }
    let degree = cs.degree();
    for lookup in cs.lookups() {
        collect(lookup.selector_expression(), &mut rotations);
        for table in lookup.table_expressions() {
            collect(table, &mut rotations);
        }
        for chunk in lookup.chunk_by_degree(degree).input_expression_chunks() {
            for input in chunk {
                for expr in input {
                    collect(expr, &mut rotations);
                }
            }
        }
    }
    rotations
}

/// Helper-chunk size vectors per lookup argument.
pub(crate) fn lookup_chunk_lens(cs: &ConstraintSystem<F>) -> Vec<Vec<usize>> {
    let degree = cs.degree();
    cs.lookups()
        .iter()
        .map(|lookup| {
            lookup
                .chunk_by_degree(degree)
                .input_expression_chunks()
                .iter()
                .map(Vec::len)
                .collect()
        })
        .collect()
}

/// Classify every lookup helper chunk with the emitter's own dispatch rule.
pub(crate) fn lookup_chunk_arms(
    inputs: &VerifierBuildInputs<'_, '_>,
    plan: &LoweringPlan,
) -> BTreeSet<LookupChunkArm> {
    let cs = inputs.vk.cs();
    let degree = cs.degree();
    let evaluator =
        crate::lowering::quotient_numerator::yul_emit::Evaluator::new(cs, &plan.meta, &plan.data);
    let mut arms = BTreeSet::new();
    for lookup in cs.lookups() {
        for chunk in lookup.chunk_by_degree(degree).input_expression_chunks() {
            let arm = match chunk.len() {
                // The k == 0 arm is documented unreachable from real
                // constraint systems (chunks are never empty); it is covered
                // by direct emitter unit tests only.
                0 => unreachable!("lookup chunks are never empty"),
                1 => LookupChunkArm::Single,
                _ if evaluator.lookup_shared_prefix_applicable(chunk) => {
                    LookupChunkArm::SharedPrefix
                }
                _ => LookupChunkArm::Staged,
            };
            arms.insert(arm);
        }
    }
    arms
}

/// Execution surfaces one finalized plan folds through.
pub(crate) fn plan_surfaces(plan: &LoweringPlan) -> BTreeSet<SurfaceKind> {
    plan.quotient
        .plan
        .identities_in_execution_order()
        .expect("finalized plan walks its execution stream")
        .iter()
        .map(|(_, kind)| SurfaceKind::of(*kind))
        .collect()
}

/// Assert one case's plan satisfies its registered coverage expectation.
pub(crate) fn assert_case_coverage(
    case: &ShapeFuzzCase,
    inputs: &VerifierBuildInputs<'_, '_>,
    plan: &LoweringPlan,
) {
    let name = case.name;
    let expectation = coverage_expectation(name);
    let cs = inputs.vk.cs();

    if let Some(expected) = expectation.cs_degree {
        assert_eq!(cs.degree(), expected, "case `{name}`: cs.degree() drifted");
    }
    if let Some(expected) = expectation.permutation_sets {
        assert_eq!(
            plan.meta.protocol.num_permutation_zs, expected,
            "case `{name}`: permutation set count drifted (chunk_len {})",
            plan.meta.protocol.permutation_chunk_len
        );
    }

    let chunk_lens = lookup_chunk_lens(cs);
    let expected_chunks: Vec<Vec<usize>> =
        expectation.lookup_chunk_lens.iter().map(|lens| lens.to_vec()).collect();
    assert_eq!(
        chunk_lens, expected_chunks,
        "case `{name}`: lookup helper-chunk shape drifted"
    );

    assert!(
        plan.meta.protocol.num_trashcans >= expectation.min_trash,
        "case `{name}`: expected at least {} trash identities, found {}",
        expectation.min_trash,
        plan.meta.protocol.num_trashcans
    );

    let surfaces = plan_surfaces(plan);
    for surface in expectation.required_surfaces {
        assert!(
            surfaces.contains(surface),
            "case `{name}`: never folds through the {surface:?} surface (reached {surfaces:?})"
        );
    }

    for op in expectation.required_ops {
        assert!(
            plan.quotient.build.used_ops.contains(op),
            "case `{name}`: finalized bytecode never uses opcode {op:#04x} (used {:?})",
            plan.quotient.build.used_ops
        );
    }

    let rotations = query_rotations(cs);
    for rotation in expectation.required_rotations {
        assert!(
            rotations.contains(rotation),
            "case `{name}`: no gate queries rotation {rotation} (queried {rotations:?})"
        );
    }

    assert!(
        plan.quotient.sorted_simple.len() >= expectation.min_selector_buckets,
        "case `{name}`: expected at least {} selector buckets, found {}",
        expectation.min_selector_buckets,
        plan.quotient.sorted_simple.len()
    );

    let max_gap = plan
        .quotient
        .plan
        .selector_fold
        .gaps_by_identity
        .iter()
        .flatten()
        .copied()
        .max()
        .unwrap_or(0);
    assert!(
        max_gap >= expectation.min_selector_gap,
        "case `{name}`: expected an intra-bucket selector gap of at least {}, found {max_gap}",
        expectation.min_selector_gap
    );

    let interpreted = plan
        .quotient
        .plan
        .identities_in_execution_order()
        .expect("finalized plan walks its execution stream")
        .iter()
        .filter(|(_, kind)| SurfaceKind::of(*kind) == SurfaceKind::Interpreted)
        .count();
    assert!(
        interpreted >= expectation.min_interpreted,
        "case `{name}`: expected at least {} interpreted identities, found {interpreted}",
        expectation.min_interpreted
    );
}

// ---------------------------------------------------------------------
// Tier-1 tests: no feature gates, no solc, no environment variables.
// ---------------------------------------------------------------------

#[cfg(all(test, not(doctest)))]
mod tests {
    use midnight_proofs::{
        dev::MockProver, plonk::keygen_vk_with_k, poly::kzg::KZGCommitmentScheme,
    };
    use rand::SeedableRng;

    use super::*;
    use crate::{
        api::{GeneratorConfig, RenderDiagnostics, RenderOptions, RenderVk},
        SolidityGenerator,
    };

    /// Per case: MockProver (provability guard for the proving-tier e2e),
    /// keygen, certified lowering plan (building `lowering_plan()` IS the
    /// certification assertion — it runs `validate_quotient_mem_ptrs`,
    /// `certify_quotient_program`, and the dual-build check, panicking on any
    /// disagreement), coverage expectation, public-API manifest cross-check,
    /// and a render smoke with explicit (non-feature-dependent) diagnostics.
    #[test]
    fn shape_corpus_cases_certify_and_cover() {
        let mut setup_rng = ChaCha8Rng::seed_from_u64(0x5c0e_c0de);
        for case in curated_cases() {
            let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
            let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);

            let committed = vec![F::ZERO];
            let public = vec![circuit.public_instance()];
            let prover =
                MockProver::run(case.k, &circuit, vec![committed, public]).unwrap_or_else(|err| {
                    panic!("case `{}`: MockProver::run failed: {err:?}", case.name)
                });
            prover.verify().unwrap_or_else(|failures| {
                panic!("case `{}`: circuit not satisfied: {failures:#?}", case.name)
            });

            let vk =
                keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
                    .unwrap_or_else(|err| {
                        panic!("case `{}`: vk generation failed: {err:?}", case.name)
                    });
            let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
            let inputs = generator.inputs();
            let plan = inputs.lowering_plan();

            assert_case_coverage(&case, &inputs, &plan);

            // Public-API cross-check, full-entry (E8/G2): the exported
            // manifest must be exactly the internal execution walk re-sorted
            // into global order -- same indices, same sources, same targets,
            // dense and complete.
            let manifest =
                generator.quotient_identity_manifest().expect("quotient identity manifest");
            let mut execution = plan
                .quotient
                .plan
                .identities_in_execution_order()
                .expect("finalized plan walks its execution stream")
                .into_iter()
                .map(|(identity, _)| identity)
                .collect::<Vec<_>>();
            execution.sort_by_key(|identity| identity.meta.global_index);
            assert_eq!(
                manifest.entries.len(),
                execution.len(),
                "case `{}`: public manifest and internal execution walk disagree",
                case.name
            );
            for (entry, identity) in manifest.entries.iter().zip(&execution) {
                assert_eq!(
                    entry.global_index, identity.meta.global_index,
                    "case `{}`: manifest global index drifted",
                    case.name
                );
                assert_eq!(
                    entry.source, identity.meta.source,
                    "case `{}`: manifest source drifted at global index {}",
                    case.name, entry.global_index
                );
            }
            assert!(
                manifest
                    .entries
                    .iter()
                    .enumerate()
                    .all(|(idx, entry)| entry.global_index == idx),
                "case `{}`: manifest global indices must be dense from zero",
                case.name
            );

            let diagnostics = RenderDiagnostics {
                trace: false,
                gas_checkpoints: false,
            };
            generator
                .render(RenderOptions {
                    vk: RenderVk::Separate,
                    diagnostics,
                    ..RenderOptions::default()
                })
                .unwrap_or_else(|err| {
                    panic!("case `{}`: verifier render failed: {err:?}", case.name)
                });
            generator.render_quotient_evaluator(diagnostics).unwrap_or_else(|err| {
                panic!("case `{}`: evaluator render failed: {err:?}", case.name)
            });
        }
    }

    /// Corpus-union floors: all six execution surfaces, the opcode floor,
    /// and both reachable lookup emission arms.
    #[test]
    fn shape_corpus_union_covers_surfaces_and_ops() {
        let mut setup_rng = ChaCha8Rng::seed_from_u64(0x5c0e_c0df);
        let mut surfaces = BTreeSet::new();
        let mut ops = BTreeSet::new();
        let mut arms = BTreeSet::new();

        for case in curated_cases() {
            assert!(
                case.k >= SHAPE_FUZZ_K,
                "case `{}`: corpus domains never shrink below the fuzzer floor",
                case.name
            );
            let circuit = ShapeFuzzCircuit::new(case.spec, case.seed);
            let params = shape_fuzz_params(&[(case.spec, case.k)], &mut setup_rng);
            let vk =
                keygen_vk_with_k::<F, KZGCommitmentScheme<Bls12>, _>(&params, &circuit, case.k)
                    .unwrap_or_else(|err| {
                        panic!("case `{}`: vk generation failed: {err:?}", case.name)
                    });
            let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
            let inputs = generator.inputs();
            let plan = inputs.lowering_plan();

            surfaces.extend(plan_surfaces(&plan));
            ops.extend(plan.quotient.build.used_ops.iter().copied());
            arms.extend(lookup_chunk_arms(&inputs, &plan));
        }

        for kind in SurfaceKind::ALL {
            assert!(
                surfaces.contains(&kind),
                "corpus union never folds through the {kind:?} surface"
            );
        }
        let missing: Vec<String> = REQUIRED_CORPUS_OPS
            .iter()
            .filter(|op| !ops.contains(op))
            .map(|op| format!("{op:#04x}"))
            .collect();
        assert!(
            missing.is_empty(),
            "corpus union never emits required opcode(s) {missing:?} (emitted {:?})",
            ops.iter().map(|op| format!("{op:#04x}")).collect::<Vec<_>>()
        );
        // The shared-prefix arm needs multi-expression inputs with adjacent
        // tail evals, which no safe axis produces yet (deferred with the
        // risky-axis follow-up); the k == 0 arm is unreachable from real
        // constraint systems. Both stay covered by emitter unit tests.
        for arm in [LookupChunkArm::Single, LookupChunkArm::Staged] {
            assert!(
                arms.contains(&arm),
                "corpus union never dispatches the {arm:?} lookup arm (reached {arms:?})"
            );
        }
    }

    /// Seed bits 0–6 keep their exact historical meaning, and the additive
    /// axes stay off unless bits 7+ request them.
    #[test]
    fn generated_specs_keep_legacy_seed_bits() {
        for seed in [0u64, 0x01, 0x2a, 0x7f] {
            let spec = generated_shape_fuzz_spec(seed);
            assert_eq!(spec.next_rotation, seed & 0x01 != 0);
            assert_eq!(spec.second_phase, seed & 0x02 != 0);
            assert_eq!(spec.permutation, seed & 0x04 != 0);
            assert_eq!(spec.lookup, seed & 0x08 != 0);
            assert_eq!(spec.additive_selector, seed & 0x10 != 0);
            assert_eq!(spec.complex_selector, seed & 0x20 != 0);
            assert_eq!(spec.fixed_scale, seed & 0x40 != 0);
            assert_eq!(spec.tag, 100 + seed.rotate_left(17) % 10_000);
            assert_eq!(spec.gate_degree_boost, 0);
            assert!(!spec.wide_permutation);
            assert_eq!(spec.lookup_parallel, 0);
            assert_eq!(spec.extra_lookup_args, 0);
            assert_eq!(spec.limb7_gates, 0);
            assert_eq!(spec.limb7_bilinear_gates, 0);
            assert_eq!(spec.selector_gate_count, 0);
            assert_eq!(spec.extra_main_gates, 0);
            assert!(!spec.pow5_gate);
            assert!(!spec.prev_rotation);
        }
    }
}

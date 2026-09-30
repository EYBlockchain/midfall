// SPDX-License-Identifier: CC0-1.0
//! Unit tests for the direct quotient lowering: shape recognition (positive
//! and negative cases, on hand-built trees that mirror
//! `circuits/src/field/foreign/util.rs` and on the real foreign-field gates
//! configured by `midnight-zk-stdlib`), fail-closed IR translation
//! validation, and the emitted Yul shape. The fold check (`folds`) is tested
//! in `lowering/tests.rs`; the emitted Yul is tested against a Rust reference
//! by the EVM-tier probe tests (`tests/common::quotient_probe`).

use std::collections::{BTreeSet, HashMap};

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Constraints, Expression},
    poly::Rotation,
};
use num_bigint::BigUint;
use ruint::aliases::U256;

use super::{
    emit,
    layout::{self as direct_layout, CopyRun, DirectLayout, DirectMemory},
    used_slots, validate, DirectCall, DirectExpr, DirectOptions, DirectQuotientProgram, DirectSlot,
    RunKind,
};
use crate::api::{
    QuotientIdentityManifest, QuotientIdentityManifestEntry, QuotientIdentityManifestTarget,
    QuotientIdentitySource,
};

// ---------------------------------------------------------------------------
// Rust helper shapes, written exactly as circuits/src/field/foreign/util.rs
// builds them (the Expression operators apply the 0 + x, 1 * x, 0 * x rules).
// ---------------------------------------------------------------------------

fn rust_sum_exprs(coeffs: &[Fq], exprs: &[Expression<Fq>]) -> Expression<Fq> {
    exprs
        .iter()
        .zip(coeffs.iter())
        .map(|(v, b)| Expression::Constant(*b) * v.clone())
        .fold(Expression::Constant(Fq::ZERO), |acc, e| acc + e)
}

fn rust_pair_wise_prod(v: &[Expression<Fq>], w: &[Expression<Fq>]) -> Vec<Expression<Fq>> {
    v.iter()
        .flat_map(|vi| w.iter().map(|wj| vi.clone() * wj.clone()).collect::<Vec<_>>())
        .collect()
}

fn big_to_fq(b: &BigUint) -> Fq {
    let r = BigUint::from_bytes_le(&(-Fq::ONE).to_repr()) + 1u32;
    let reduced = b % &r;
    let mut bytes = reduced.to_bytes_le();
    bytes.resize(32, 0);
    let mut repr = <Fq as PrimeField>::Repr::default();
    repr.as_mut().copy_from_slice(&bytes);
    Fq::from_repr(repr).unwrap()
}

/// Emulated-field parameters of a foreign-field gate (params.rs style).
struct FfParams {
    nb_limbs: usize,
    log2_base: u32,
    modulus: BigUint,
    moduli: Vec<BigUint>,
}

impl FfParams {
    fn bls12_381_fp() -> Self {
        let modulus = BigUint::parse_bytes(
            b"1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab",
            16,
        )
        .unwrap();
        let two134 = BigUint::from(1u32) << 134u32;
        Self {
            nb_limbs: 7,
            log2_base: 56,
            modulus,
            moduli: vec![two134.clone(), two134 - 1u32],
        }
    }

    /// A different (made-up) emulation, to show nothing is hard-coded.
    fn toy() -> Self {
        let modulus = (BigUint::from(1u32) << 250u32) - 189u32;
        let two90 = BigUint::from(1u32) << 90u32;
        Self {
            nb_limbs: 5,
            log2_base: 52,
            modulus,
            moduli: vec![two90 + 3u32],
        }
    }

    fn base_powers(&self) -> Vec<BigUint> {
        (0..self.nb_limbs)
            .map(|i| (BigUint::from(1u32) << (self.log2_base * i as u32)) % &self.modulus)
            .collect()
    }

    fn double_base_powers(&self) -> Vec<BigUint> {
        (0..self.nb_limbs)
            .flat_map(|i| {
                (0..self.nb_limbs).map(move |j| {
                    (BigUint::from(1u32) << (self.log2_base * (i + j) as u32)) % &self.modulus
                })
            })
            .collect()
    }
}

fn to_fq(v: &[BigUint]) -> Vec<Fq> {
    v.iter().map(big_to_fq).collect()
}

fn limbs(
    meta: &mut midnight_proofs::plonk::VirtualCells<'_, Fq>,
    cols: &[Column<Advice>],
    rot: Rotation,
) -> Vec<Expression<Fq>> {
    cols.iter().map(|c| meta.query_advice(*c, rot)).collect()
}

/// Constraint system with a mul-like gate (mul.rs shape) and a norm-like gate
/// (norm.rs shape) for `params`, plus any extra gates.
fn ff_constraint_system(
    params: &FfParams,
    extra: impl FnOnce(&mut ConstraintSystem<Fq>, &[Column<Advice>]),
) -> ConstraintSystem<Fq> {
    let mut cs = ConstraintSystem::<Fq>::default();
    let n = params.nb_limbs;
    let cols: Vec<Column<Advice>> = (0..2 * n + 1).map(|_| cs.advice_column()).collect();
    let (xy_cols, z_cols) = (cols[..n].to_vec(), cols[n..2 * n].to_vec());
    let bp = params.base_powers();
    let dbp = params.double_base_powers();
    let m = params.modulus.clone();
    let moduli = params.moduli.clone();
    let (bp2, dbp2, moduli2, m2) = (bp.clone(), dbp.clone(), moduli.clone(), m.clone());
    let (xy2, z2) = (xy_cols.clone(), z_cols.clone());
    cs.create_gate("ff mul", move |meta| {
        let xs = limbs(meta, &xy_cols, Rotation::cur());
        let ys = limbs(meta, &xy_cols, Rotation::next());
        let zs = limbs(meta, &z_cols, Rotation::cur());
        let u = meta.query_advice(z_cols[0], Rotation::next());
        let vs = limbs(meta, &z_cols[1..=moduli.len()], Rotation::next());
        let xys = rust_pair_wise_prod(&xs, &ys);
        let k_min = Expression::Constant(Fq::from(12345u64));
        let native = rust_sum_exprs(&to_fq(&dbp), &xys)
            + rust_sum_exprs(&to_fq(&bp), &xs)
            + rust_sum_exprs(&to_fq(&bp), &ys)
            - rust_sum_exprs(&to_fq(&bp), &zs)
            - (u.clone() + k_min) * Expression::Constant(big_to_fq(&m));
        let mut ids: Vec<(&'static str, Expression<Fq>)> = moduli
            .iter()
            .zip(vs)
            .map(|(mj, vj)| {
                let bij: Vec<BigUint> = dbp.iter().map(|b| b % mj).collect();
                let bi: Vec<BigUint> = bp.iter().map(|b| b % mj).collect();
                (
                    "mod",
                    rust_sum_exprs(&to_fq(&bij), &xys)
                        + rust_sum_exprs(&to_fq(&bi), &xs)
                        + rust_sum_exprs(&to_fq(&bi), &ys)
                        - rust_sum_exprs(&to_fq(&bi), &zs)
                        - u.clone() * Expression::Constant(big_to_fq(&(&m % mj)))
                        - (vj + Expression::Constant(Fq::from(77u64)))
                            * Expression::Constant(big_to_fq(mj)),
                )
            })
            .collect();
        ids.push(("native", native));
        Constraints::without_selector(ids)
    });
    cs.create_gate("ff norm", move |meta| {
        let xs = limbs(meta, &xy2, Rotation::cur());
        let zs = limbs(meta, &z2, Rotation::cur());
        let u = meta.query_advice(z2[0], Rotation::next());
        let shift = Expression::Constant(Fq::from(1u64 << 40));
        let shifted: Vec<Expression<Fq>> = xs.iter().map(|x| x + &shift).collect();
        let mut ids: Vec<(&'static str, Expression<Fq>)> = moduli2
            .iter()
            .map(|mj| {
                let bi: Vec<BigUint> = bp2.iter().map(|b| b % mj).collect();
                (
                    "mod",
                    rust_sum_exprs(&to_fq(&bi), &shifted)
                        - rust_sum_exprs(&to_fq(&bi), &zs)
                        - u.clone() * Expression::Constant(big_to_fq(&(&m2 % mj))),
                )
            })
            .collect();
        ids.push((
            "native",
            rust_sum_exprs(&to_fq(&bp2), &shifted)
                - rust_sum_exprs(&to_fq(&bp2), &zs)
                - u * Expression::Constant(big_to_fq(&m2)),
        ));
        let _ = &dbp2;
        Constraints::without_selector(ids)
    });
    extra(&mut cs, &cols);
    cs
}

/// Manifest with every gate polynomial fully evaluated and no families.
fn gates_only_manifest(
    polys: &[(usize, &str, usize, &Expression<Fq>)],
) -> QuotientIdentityManifest {
    QuotientIdentityManifest {
        entries: polys
            .iter()
            .enumerate()
            .map(|(j, (g, name, p, _))| QuotientIdentityManifestEntry {
                global_index: j,
                source: QuotientIdentitySource::Gate {
                    gate_index: *g,
                    gate_name: name.to_string(),
                    constraint_index: *p,
                    constraint_name: String::new(),
                    polynomial_index: *p,
                },
                target: QuotientIdentityManifestTarget::Main,
            })
            .collect(),
        gate_identities: polys.len(),
        permutation_identities: 0,
        lookup_identities: 0,
        trash_identities: 0,
        simple_selector_cols: Vec::new(),
    }
}

/// Replace virtual selectors by the constant one (the value the Rust verifier
/// substitutes for a simple selector), for raw `configure` trees.
fn strip_selectors(e: &Expression<Fq>) -> Expression<Fq> {
    match e {
        Expression::Selector(_) => Expression::Constant(Fq::ONE),
        Expression::Negated(a) => Expression::Negated(Box::new(strip_selectors(a))),
        Expression::Sum(a, b) => {
            Expression::Sum(Box::new(strip_selectors(a)), Box::new(strip_selectors(b)))
        }
        Expression::Product(a, b) => {
            Expression::Product(Box::new(strip_selectors(a)), Box::new(strip_selectors(b)))
        }
        Expression::Scaled(a, c) => Expression::Scaled(Box::new(strip_selectors(a)), *c),
        other => other.clone(),
    }
}

fn program_for_cs(cs: &ConstraintSystem<Fq>, options: DirectOptions) -> DirectQuotientProgram {
    let stripped: Vec<(usize, String, usize, Expression<Fq>)> = cs
        .gates()
        .iter()
        .enumerate()
        .flat_map(|(g, gate)| {
            gate.polynomials()
                .iter()
                .enumerate()
                .map(move |(p, poly)| (g, gate.name().to_string(), p, strip_selectors(poly)))
        })
        .collect();
    let polys: Vec<(usize, &str, usize, &Expression<Fq>)> =
        stripped.iter().map(|(g, n, p, e)| (*g, n.as_str(), *p, e)).collect();
    let advice_queries: Vec<(usize, i32)> =
        cs.advice_queries().iter().map(|(c, r)| (c.index(), r.0)).collect();
    DirectQuotientProgram::build_from_polys(
        &polys,
        &advice_queries,
        &gates_only_manifest(&polys),
        options,
    )
    .expect("direct program builds")
}

fn sample(seed: u64, i: usize) -> Fq {
    Fq::from(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (i as u64).wrapping_mul(0xc2b2_ae3d))
        .pow_vartime([7u64])
        + Fq::from(i as u64)
}

/// Semantic evaluation of the IR (no memory layout).
fn semantic(program: &DirectQuotientProgram, e: &DirectExpr, v: &HashMap<DirectSlot, Fq>) -> Fq {
    let limb = |vector: usize, i: usize| -> Fq {
        let vec = &program.vectors[vector];
        let base = v[&vec.slot(i)];
        base + vec.shift.map(|(_, s)| s).unwrap_or(Fq::ZERO)
    };
    match e {
        DirectExpr::Constant(c) => *c,
        DirectExpr::SimpleSelector(_) => Fq::ONE,
        DirectExpr::Slot(s) => v[s],
        DirectExpr::Negated(a) => -semantic(program, a, v),
        DirectExpr::Sum(a, b) => semantic(program, a, v) + semantic(program, b, v),
        DirectExpr::Product(a, b) => semantic(program, a, v) * semantic(program, b, v),
        DirectExpr::Call(DirectCall::SumExprs { run, vector }) => program.runs[*run]
            .values
            .iter()
            .enumerate()
            .map(|(i, c)| *c * limb(*vector, i))
            .sum(),
        DirectExpr::Call(DirectCall::SumExprsByDegree { run, table }) => {
            let t = &program.tables[*table];
            let (nx, ny) = (program.vectors[t.xs].len, program.vectors[t.ys].len);
            let mut tt = vec![Fq::ZERO; nx + ny - 1];
            for i in 0..nx {
                for j in 0..ny {
                    tt[i + j] += limb(t.xs, i) * limb(t.ys, j);
                }
            }
            program.runs[*run].values.iter().zip(tt).map(|(c, x)| *c * x).sum()
        }
    }
}

fn reference(e: &Expression<Fq>, v: &HashMap<DirectSlot, Fq>) -> Fq {
    e.evaluate(
        &|c| c,
        &|_| Fq::ONE,
        &|q| {
            v[&DirectSlot::Fixed {
                column: q.column_index(),
                rotation: q.rotation().0,
            }]
        },
        &|q| {
            v[&DirectSlot::Advice {
                column: q.column_index(),
                rotation: q.rotation().0,
            }]
        },
        &|q| {
            v[&DirectSlot::Instance {
                column: q.column_index(),
                rotation: q.rotation().0,
            }]
        },
        &|c| v[&DirectSlot::Challenge { index: c.index() }],
        &|a| -a,
        &|a, b| a + b,
        &|a, b| a * b,
        &|a, c| a * c,
    )
}

/// Assert the IR of every identity equals its source tree at a few points.
fn assert_semantically_equal(program: &DirectQuotientProgram) {
    let slots: Vec<DirectSlot> = used_slots(program).into_iter().collect();
    for seed in 1..=3u64 {
        let values: HashMap<DirectSlot, Fq> =
            slots.iter().enumerate().map(|(i, s)| (*s, sample(seed, i))).collect();
        for identity in &program.gates {
            assert_eq!(
                semantic(program, &identity.expr, &values),
                reference(&identity.source, &values),
                "identity {} of gate {}",
                identity.global_index,
                identity.gate_name
            );
        }
    }
}

fn calls(program: &DirectQuotientProgram, gate: &str) -> (usize, usize) {
    let mut out = (0, 0);
    for identity in program.gates.iter().filter(|g| g.gate_name == gate) {
        direct_layout::visit_calls(&identity.expr, &mut |c| match c {
            DirectCall::SumExprs { .. } => out.0 += 1,
            DirectCall::SumExprsByDegree { .. } => out.1 += 1,
        });
    }
    out
}

// ---------------------------------------------------------------------------
// Shape recognition: positive cases
// ---------------------------------------------------------------------------

#[test]
fn recognises_sum_exprs_and_pair_wise_prod_shapes_generically() {
    for params in [FfParams::bls12_381_fp(), FfParams::toy()] {
        let n = params.nb_limbs;
        let cs = ff_constraint_system(&params, |_, _| {});
        let program = program_for_cs(&cs, DirectOptions::default());
        // Vectors: xs (cur), ys (next), zs (cur), plus the shifted xs view.
        let bases: Vec<_> = program.vectors.iter().filter(|v| v.shift.is_none()).collect();
        assert_eq!(bases.len(), 3, "{:?}", program.vectors);
        assert!(bases.iter().all(|v| v.len == n));
        assert_eq!(
            program.vectors.iter().filter(|v| v.shift.is_some()).count(),
            1
        );
        // mul: every polynomial has 3 sum_exprs (xs, ys, zs) and 1 by-degree call.
        let polys = params.moduli.len() + 1;
        assert_eq!(calls(&program, "ff mul"), (3 * polys, polys));
        // norm: sum_exprs over the shifted view and over zs.
        assert_eq!(calls(&program, "ff norm"), (2 * polys, 0));
        // One product table for the mul gate, 2n-1 entries.
        assert_eq!(program.tables.len(), 1);
        assert_eq!(program.tables[0].len, 2 * n - 1);
        for run in &program.runs {
            match run.kind {
                RunKind::Linear => assert_eq!(run.values.len(), n),
                RunKind::ByDegree => assert_eq!(run.values.len(), 2 * n - 1),
            }
        }
        assert_semantically_equal(&program);
    }
}

#[test]
fn zero_coefficients_are_kept_in_runs() {
    // Reducing 2^(56 i) mod m by 2^134 zeroes limbs 3..6: those terms are
    // absent from the Rust tree and must reappear as zeros in the run.
    let params = FfParams::bls12_381_fp();
    let cs = ff_constraint_system(&params, |_, _| {});
    let program = program_for_cs(&cs, DirectOptions::default());
    let two134 = BigUint::from(1u32) << 134u32;
    let expected: Vec<Fq> =
        params.base_powers().iter().map(|b| big_to_fq(&(b % &two134))).collect();
    assert!(expected[3..].iter().all(|c| *c == Fq::ZERO));
    assert!(program
        .runs
        .iter()
        .any(|run| run.kind == RunKind::Linear && run.values == expected));
    // By-degree run for mj = 2^134: degrees 3..6 vanish.
    let dbp_by_degree: Vec<Fq> = (0..13)
        .map(|t| {
            big_to_fq(&(((BigUint::from(1u32) << (56 * t as u32)) % &params.modulus) % &two134))
        })
        .collect();
    assert!(program
        .runs
        .iter()
        .any(|run| run.kind == RunKind::ByDegree && run.values == dbp_by_degree));
}

#[test]
fn real_stdlib_foreign_field_and_ec_gates_are_recognised() {
    use midnight_zk_stdlib::{ZkStdLib, ZkStdLibArch};
    let mut cs = ConstraintSystem::<Fq>::default();
    let _ = ZkStdLib::configure(
        &mut cs,
        (
            ZkStdLibArch {
                bls12_381: true,
                ..ZkStdLibArch::default()
            },
            16,
        ),
    );
    let program = program_for_cs(&cs, DirectOptions::default());
    for gate in [
        "Foreign-field multiplication",
        "Foreign-field normalization",
        "Foreign-field EC is_on_curve",
        "Foreign-field EC lambda slope",
        "Foreign-field EC assert_tangent",
        "Foreign-field EC assert_lambda_squared",
    ] {
        let (sums, by_degree) = calls(&program, gate);
        assert!(sums > 0, "no sum_exprs recognised in {gate}");
        if gate != "Foreign-field normalization" {
            assert!(by_degree > 0, "no pair_wise_prod sum recognised in {gate}");
        }
    }
    assert!(
        program.vectors.iter().any(|v| v.shift.is_some()),
        "norm.rs shifted_x"
    );
    assert_semantically_equal(&program);
}

// ---------------------------------------------------------------------------
// Shape recognition: negative cases (everything stays plain transliteration)
// ---------------------------------------------------------------------------

/// Constraint system with one product-chain gate that establishes vectors
/// a0..a{n-1} @ cur and @ next, plus `gate(meta, cols)`.
fn with_vectors(
    n: usize,
    gate: impl FnOnce(
            &mut midnight_proofs::plonk::VirtualCells<'_, Fq>,
            &[Column<Advice>],
        ) -> Expression<Fq>
        + 'static,
) -> DirectQuotientProgram {
    let mut cs = ConstraintSystem::<Fq>::default();
    let cols: Vec<Column<Advice>> = (0..n + 2).map(|_| cs.advice_column()).collect();
    let c1 = cols.clone();
    cs.create_gate("vectors", move |meta| {
        let xs = limbs(meta, &c1[..n], Rotation::cur());
        let ys = limbs(meta, &c1[..n], Rotation::next());
        let coeffs: Vec<Fq> = (0..n * n)
            .map(|k| Fq::from(3u64).pow_vartime([(k / n + k % n) as u64]))
            .collect();
        Constraints::without_selector(vec![(
            "chain",
            rust_sum_exprs(&coeffs, &rust_pair_wise_prod(&xs, &ys)),
        )])
    });
    let c2 = cols.clone();
    cs.create_gate("probe", move |meta| {
        let e = gate(meta, &c2);
        Constraints::without_selector(vec![("probe", e)])
    });
    let program = program_for_cs(&cs, DirectOptions::default());
    assert_eq!(
        calls(&program, "vectors"),
        (0, 1),
        "the vector-defining chain is a by-degree sum"
    );
    assert_semantically_equal(&program);
    program
}

#[test]
fn linear_chain_over_known_vector_is_recognised() {
    let program = with_vectors(4, |meta, cols| {
        let xs = limbs(meta, &cols[..4], Rotation::cur());
        rust_sum_exprs(
            &[Fq::from(2u64), Fq::ZERO, Fq::from(5u64), Fq::from(9u64)],
            &xs,
        )
    });
    assert_eq!(calls(&program, "probe"), (1, 0));
}

#[test]
fn non_degree_coefficients_stay_plain() {
    // c_ij = 2^i * 3^j is not a function of i + j.
    let program = with_vectors(4, |meta, cols| {
        let xs = limbs(meta, &cols[..4], Rotation::cur());
        let ys = limbs(meta, &cols[..4], Rotation::next());
        let coeffs: Vec<Fq> = (0..16)
            .map(|k| {
                Fq::from(2u64).pow_vartime([(k / 4) as u64])
                    * Fq::from(3u64).pow_vartime([(k % 4) as u64])
            })
            .collect();
        rust_sum_exprs(&coeffs, &rust_pair_wise_prod(&xs, &ys))
    });
    assert_eq!(calls(&program, "probe"), (0, 0));
}

#[test]
fn mixed_rotation_linear_chain_stays_plain() {
    let program = with_vectors(4, |meta, cols| {
        let mut v = limbs(meta, &cols[..4], Rotation::cur());
        v[2] = meta.query_advice(cols[2], Rotation::next());
        rust_sum_exprs(
            &[
                Fq::from(2u64),
                Fq::from(3u64),
                Fq::from(5u64),
                Fq::from(7u64),
            ],
            &v,
        )
    });
    assert_eq!(calls(&program, "probe"), (0, 0));
}

#[test]
fn out_of_order_limbs_stay_plain() {
    let program = with_vectors(4, |meta, cols| {
        let mut v = limbs(meta, &cols[..4], Rotation::cur());
        v.swap(1, 2);
        rust_sum_exprs(
            &[
                Fq::from(2u64),
                Fq::from(3u64),
                Fq::from(5u64),
                Fq::from(7u64),
            ],
            &v,
        )
    });
    assert_eq!(calls(&program, "probe"), (0, 0));
}

#[test]
fn limbs_outside_every_vector_stay_plain() {
    // Columns n, n+1 are never part of a product chain, so no vector covers them.
    let program = with_vectors(4, |meta, cols| {
        let v = limbs(meta, &cols[4..6], Rotation::cur());
        rust_sum_exprs(&[Fq::from(2u64), Fq::from(3u64)], &v)
    });
    assert_eq!(calls(&program, "probe"), (0, 0));
}

#[test]
fn inconsistent_shift_stays_plain() {
    let program = with_vectors(4, |meta, cols| {
        let xs = limbs(meta, &cols[..4], Rotation::cur());
        let shifted: Vec<Expression<Fq>> = xs
            .iter()
            .enumerate()
            .map(|(i, x)| x + &Expression::Constant(Fq::from(1000 + i as u64)))
            .collect();
        rust_sum_exprs(
            &[
                Fq::from(2u64),
                Fq::from(3u64),
                Fq::from(5u64),
                Fq::from(7u64),
            ],
            &shifted,
        )
    });
    assert_eq!(calls(&program, "probe"), (0, 0));
}

#[test]
fn vector_needs_every_column_queried() {
    // A product chain over columns {0, 1, 3} (column 2 never queried at that
    // rotation) does not define a vector.
    let mut cs = ConstraintSystem::<Fq>::default();
    let cols: Vec<Column<Advice>> = (0..4).map(|_| cs.advice_column()).collect();
    cs.create_gate("gappy", move |meta| {
        let xs: Vec<_> =
            [0, 1, 3].iter().map(|i| meta.query_advice(cols[*i], Rotation::cur())).collect();
        let ys: Vec<_> = [0, 1, 3]
            .iter()
            .map(|i| meta.query_advice(cols[*i], Rotation::next()))
            .collect();
        let coeffs = vec![Fq::ONE; 9];
        Constraints::without_selector(vec![(
            "chain",
            rust_sum_exprs(&coeffs, &rust_pair_wise_prod(&xs, &ys)),
        )])
    });
    let program = program_for_cs(&cs, DirectOptions::default());
    assert!(program.vectors.is_empty());
    assert_eq!(calls(&program, "gappy"), (0, 0));
    assert_semantically_equal(&program);
}

#[test]
fn recognition_can_be_disabled() {
    let cs = ff_constraint_system(&FfParams::toy(), |_, _| {});
    let program = program_for_cs(
        &cs,
        DirectOptions {
            recognize_shapes: false,
            shifted_vectors: false,
        },
    );
    assert!(program.vectors.is_empty() && program.runs.is_empty() && program.tables.is_empty());
    assert_semantically_equal(&program);
}

// ---------------------------------------------------------------------------
// Fail-closed translation validation on a bound layout
// ---------------------------------------------------------------------------

/// Bind a program to a synthetic memory map in which the limbs of every
/// vector are split at column 3 (so views must be copied).
fn bind_synthetic(program: &DirectQuotientProgram) -> (DirectLayout, Vec<U256>) {
    let slots: Vec<DirectSlot> = used_slots(program).into_iter().collect();
    let addr_of: HashMap<DirectSlot, usize> = slots
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let gap = match s {
                DirectSlot::Advice { column, .. } if *column >= 3 => 3 * 0x20,
                _ => 0,
            };
            (*s, 0x1000 + i * 0x20 + gap)
        })
        .collect();
    let resolve = |s: DirectSlot| addr_of.get(&s).copied().ok_or_else(|| format!("unbound {s:?}"));
    let gate_words = direct_layout::gate_scratch_words(program, &resolve).unwrap();
    let layout = DirectLayout::bind(
        program,
        DirectMemory {
            selector_acc_mptr: 0x8000,
            state_mptr: 0x8100,
            state_words: direct_layout::state_words(program),
            stack_mptr: 0x9000,
            stack_words: gate_words,
            const_table_mptr: 0x4000,
            family_scratch_words: 0,
        },
        resolve,
    )
    .unwrap();
    let table = program.table_words().into_iter().map(|w| w.value).collect();
    (layout, table)
}

fn validation_program() -> DirectQuotientProgram {
    program_for_cs(
        &ff_constraint_system(&FfParams::bls12_381_fp(), |_, _| {}),
        DirectOptions::default(),
    )
}

#[test]
fn validation_accepts_the_bound_program() {
    let program = validation_program();
    let (layout, table) = bind_synthetic(&program);
    assert!(
        !layout.view_copies.is_empty(),
        "synthetic layout must exercise view copies"
    );
    validate::validate(&program, &layout, &table, b"seed").expect("valid lowering");
}

#[test]
fn validation_rejects_corrupted_coefficient_run() {
    let mut program = validation_program();
    let run = program.runs.iter().position(|r| r.kind == RunKind::Linear).unwrap();
    // A zero coefficient (absent from the Rust tree) is the subtle case.
    let zero = program.runs[run].values.iter().position(|c| *c == Fq::ZERO).unwrap_or(0);
    program.runs[run].values[zero] += Fq::ONE;
    let (layout, table) = bind_synthetic(&program);
    let err = validate::validate(&program, &layout, &table, b"seed").unwrap_err();
    assert!(err.contains("differs from Expression::evaluate"), "{err}");
}

#[test]
fn validation_rejects_corrupted_by_degree_run() {
    let mut program = validation_program();
    let run = program.runs.iter().position(|r| r.kind == RunKind::ByDegree).unwrap();
    program.runs[run].values[7] += Fq::ONE;
    let (layout, table) = bind_synthetic(&program);
    assert!(validate::validate(&program, &layout, &table, b"seed").is_err());
}

#[test]
fn validation_rejects_corrupted_ir_constant() {
    let mut program = validation_program();
    fn bump(e: &mut DirectExpr) -> bool {
        match e {
            DirectExpr::Constant(c) => {
                *c += Fq::ONE;
                true
            }
            DirectExpr::Negated(a) => bump(a),
            DirectExpr::Sum(a, b) | DirectExpr::Product(a, b) => bump(a) || bump(b),
            _ => false,
        }
    }
    assert!(bump(&mut program.gates[0].expr));
    program.pool = {
        // Keep the pool consistent with the corrupted tree so only the
        // arithmetic differs.
        let mut p = program.pool.clone();
        let mut stack = vec![program.gates[0].expr.clone()];
        while let Some(e) = stack.pop() {
            match e {
                DirectExpr::Constant(c) if super::is_pooled(&c) && !p.contains(&c) => p.push(c),
                DirectExpr::Negated(a) => stack.push(*a),
                DirectExpr::Sum(a, b) | DirectExpr::Product(a, b) => {
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        p
    };
    let (layout, table) = bind_synthetic(&program);
    assert!(validate::validate(&program, &layout, &table, b"seed").is_err());
}

#[test]
fn validation_rejects_corrupted_vk_table_word() {
    let program = validation_program();
    let (layout, mut table) = bind_synthetic(&program);
    table[1] += U256::from(1u64);
    assert!(validate::validate(&program, &layout, &table, b"seed").is_err());
}

#[test]
fn validation_rejects_wrong_vector_pointer_and_view_copy() {
    let program = validation_program();
    // Two vectors aliasing one view (swapping two pointers consistently would
    // only relabel memory, which is not an error).
    let (mut layout, table) = bind_synthetic(&program);
    layout.vector_addr[0] = layout.vector_addr[1];
    assert!(validate::validate(&program, &layout, &table, b"seed").is_err());

    let (mut layout, table) = bind_synthetic(&program);
    let run: &mut CopyRun = &mut layout.view_copies[0].1[0];
    run.src += 0x20;
    assert!(validate::validate(&program, &layout, &table, b"seed").is_err());
}

#[test]
fn validation_rejects_non_canonical_table_word() {
    let program = validation_program();
    let (layout, mut table) = bind_synthetic(&program);
    table[0] = U256::MAX;
    let err = validate::validate(&program, &layout, &table, b"seed").unwrap_err();
    assert!(err.contains("canonical"), "{err}");
}

// ---------------------------------------------------------------------------
// Emission shape
// ---------------------------------------------------------------------------

#[test]
fn emitted_identities_have_headers_named_constants_and_explicit_fold() {
    let program = validation_program();
    let (layout, _) = bind_synthetic(&program);
    let yul = emit::quotient_block(&program, &layout, &Default::default(), None);
    let block = [yul.functions, yul.section].concat().join("\n");
    let m = program.m;
    for identity in &program.gates {
        let j = identity.global_index;
        assert!(block.contains(&format!("function q_identity_{j}(r) {{")));
        assert!(block.contains(&format!("// identity j = {j}  (of m = {m})")));
        assert!(block.contains(&format!("mulmod(mload(YP_{}), e, r)", m - 1 - j)));
        assert!(block.contains(&format!("q_identity_{j}(q_r)")));
    }
    // Helper calls are preceded by their spelled-out terms, and helpers stay
    // out of line through the never-taken recursive call.
    assert!(block.contains("// sum_exprs(COEFF_RUN_0, "));
    assert!(block.contains("// sum_exprs_by_degree(COEFF_RUN_BY_DEGREE_0, "));
    assert!(block.contains("if iszero(coeffs) { s := sum_exprs(coeffs, exprs) leave }"));
    assert!(block.contains("if iszero(r) { leave }"));
    assert!(block.contains("pair_wise_prod_by_degree(T_G0_"));
    assert!(block.contains("mstore(Q_R_MPTR, r)"));
    // No absolute evaluation addresses inside identity bodies: slots are named.
    if let Some(line) = block.lines().find(|l| l.contains("mload(0x")) {
        panic!("identity code uses an unnamed memory slot: {line}");
    }
    let constants = emit::solidity_constants(&program, &layout).join("\n");
    for slot in used_slots(&program) {
        assert!(constants.contains(&format!("uint256 internal constant {}", slot.name())));
    }
    for (i, _) in program.pool.iter().enumerate() {
        assert!(constants.contains(&format!("QC_{i} ")));
    }
    let names: BTreeSet<&str> = program.runs.iter().map(|r| r.name.as_str()).collect();
    for name in names {
        assert!(constants.contains(name));
    }
}

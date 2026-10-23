// SPDX-License-Identifier: CC0-1.0
//! Tests for the quotient-VM listing, manifest and host-side decoder.

use std::collections::BTreeMap;

use ff::{Field, PrimeField};
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Constraints,
        Error as PlonkError, Expression, Fixed, Instance, Selector, VerifyingKey,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use ruint::aliases::U256;

use super::{
    blocks::{extract_program_blocks, render_program_blocks, ListingSymbols},
    eval_quotient_expr,
    poly::Poly,
    QuotientListingContext,
};
use crate::{
    api::{GeneratorConfig, RenderOptions, RenderVk},
    lowering::{
        encoding::fe_to_u256,
        quotient_numerator::vm::{
            disasm::{
                decode_vm_program, eval_vm_identity, relocate_vm_pointers, split_vm_items,
                VmItemKind, VmValues,
            },
            quotient_bytecode_ops, QuotientExpr, QuotientMem, QuotientProgramBuilder,
            QuotientTarget, QUOTIENT_OPCODE_TABLE, Q_OP_ADD, Q_OP_ADD_CONST, Q_OP_ADD_CONST_U8,
            Q_OP_ADD_MEM_U16, Q_OP_ADD_MUL_CONST_U8_MEM_U16, Q_OP_ADD_MUL_MEM_MEM,
            Q_OP_ADD_MUL_MEM_MEM_CONST_U8, Q_OP_AFFINE_SUM, Q_OP_BILIN7_PAIRWISE, Q_OP_BILIN7_ROW,
            Q_OP_FOLD_MAIN, Q_OP_FOLD_SELECTOR, Q_OP_LIN7, Q_OP_MODARITH7, Q_OP_MUL,
            Q_OP_MUL_CONST, Q_OP_MUL_CONST_U8, Q_OP_MUL_MEM_U16, Q_OP_NATIVE_IDENTITY,
            Q_OP_NATIVE_LOOKUP, Q_OP_NATIVE_PERMUTATION, Q_OP_NEG, Q_OP_POW5, Q_OP_PUSH_CONST,
            Q_OP_PUSH_CONST_U8, Q_OP_PUSH_MEM_LITERAL, Q_OP_PUSH_MEM_TOKEN,
            Q_OP_PUSH_MEM_TOKEN_OFFSET, Q_OP_PUSH_MEM_U16, Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16,
            Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8,
        },
    },
    SolidityGenerator,
};

// ---------------------------------------------------------------------------
// Synthetic circuit exercising simple selectors, a main-bucket gate, pow5,
// affine products, instance queries, seven-limb shapes, a permutation, a
// lookup and a trash argument.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct ListingConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    d: Column<Advice>,
    x: [Column<Advice>; 7],
    z: [Column<Advice>; 7],
    y: Column<Advice>,
    w: Column<Advice>,
    f: Column<Fixed>,
    table: Column<Fixed>,
    selectors: Vec<Selector>,
    lookup_selector: Selector,
    trash_selector: Selector,
}

#[derive(Clone, Debug, Default)]
struct ListingCircuit;

impl Circuit<Fq> for ListingCircuit {
    type Config = ListingConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let d = meta.advice_column();
        let x = std::array::from_fn(|_| meta.advice_column());
        let z = std::array::from_fn(|_| meta.advice_column());
        let y = meta.advice_column();
        let w = meta.advice_column();
        let f = meta.fixed_column();
        let table = meta.fixed_column();
        let committed: Column<Instance> = meta.instance_column();
        let public: Column<Instance> = meta.instance_column();
        meta.enable_equality(a);
        meta.enable_equality(b);
        let selectors = (0..9).map(|_| meta.selector()).collect::<Vec<_>>();
        let lookup_selector = meta.complex_selector();
        let trash_selector = meta.complex_selector();
        let pow =
            |base: u64, e: u32| Expression::Constant(Fq::from(base).pow_vartime([u64::from(e)]));

        meta.create_gate("g0 sum", |meta| {
            let (a, b, c) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::cur()),
            );
            Constraints::with_selector(selectors[0], vec![("sum", a + b - c)])
        });
        meta.create_gate("g1 pair", |meta| {
            let (a, b, c, d) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::cur()),
                meta.query_advice(d, Rotation::cur()),
            );
            Constraints::with_selector(
                selectors[1],
                vec![("mul", a.clone() * b.clone() - c), ("lin", a - b + d)],
            )
        });
        meta.create_gate("g2 sbox", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let d = meta.query_advice(d, Rotation::cur());
            let c = Expression::Constant(Fq::from(11u64));
            let t = a + c;
            Constraints::with_selector(
                selectors[2],
                vec![(
                    "pow5",
                    t.clone() * t.clone() * t.clone() * t.clone() * t - d,
                )],
            )
        });
        meta.create_gate("g3 fixed next", |meta| {
            let (f, a, b, c_next) = (
                meta.query_fixed(f, Rotation::cur()),
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::next()),
            );
            Constraints::with_selector(
                selectors[3],
                vec![(
                    "fixed",
                    f * a + b * Expression::Constant(Fq::from(3u64)) - c_next,
                )],
            )
        });
        meta.create_gate("g4 affine", |meta| {
            let (a, b, c, d) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::cur()),
                meta.query_advice(d, Rotation::cur()),
            );
            let expr = a.clone() * b.clone() * Expression::Constant(Fq::from(7u64))
                + c.clone() * d.clone() * Expression::Constant(-Fq::from(2u64))
                + a.clone() * Expression::Constant(Fq::from(5u64))
                + b.clone() * Expression::Constant(Fq::from(9u64))
                + c.clone() * a.clone() * Expression::Constant(Fq::from(13u64))
                + d * Expression::Constant(Fq::from(1u64 << 40));
            Constraints::with_selector(selectors[4], vec![("affine", expr)])
        });
        meta.create_gate("g5 main", |meta| {
            let (a, b, c) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::prev()),
                meta.query_advice(c, Rotation::cur()),
            );
            let f = meta.query_fixed(f, Rotation::cur());
            // No simple selector: the identity folds into the main bucket.
            Constraints::without_selector(vec![("main", f * (a.clone() - b) * (a - c))])
        });
        meta.create_gate("g6 instance", |meta| {
            let (committed, public, a) = (
                meta.query_instance(committed, Rotation::cur()),
                meta.query_instance(public, Rotation::cur()),
                meta.query_advice(a, Rotation::cur()),
            );
            Constraints::with_selector(selectors[5], vec![("pi", committed + public - a)])
        });
        meta.create_gate("g7 lin7", |meta| {
            let limbs = x.map(|col| meta.query_advice(col, Rotation::cur()));
            let y = meta.query_advice(y, Rotation::cur());
            let sum = limbs
                .iter()
                .enumerate()
                .map(|(i, limb)| limb.clone() * pow(2, 56 * i as u32))
                .reduce(|acc, term| acc + term)
                .expect("seven limbs");
            Constraints::with_selector(selectors[6], vec![("lin7", sum - y)])
        });
        meta.create_gate("g8 pairwise", |meta| {
            let xs = x.map(|col| meta.query_advice(col, Rotation::cur()));
            let zs = z.map(|col| meta.query_advice(col, Rotation::cur()));
            let w = meta.query_advice(w, Rotation::cur());
            let mut sum = Expression::Constant(Fq::ZERO);
            for (i, xi) in xs.iter().enumerate() {
                for (j, zj) in zs.iter().enumerate() {
                    sum = sum + xi.clone() * zj.clone() * pow(3, (i + j) as u32);
                }
            }
            Constraints::with_selector(selectors[7], vec![("pairwise", sum - w)])
        });
        meta.create_gate("g9 row", |meta| {
            let x0 = meta.query_advice(x[0], Rotation::cur());
            let zs = z.map(|col| meta.query_advice(col, Rotation::cur()));
            let w = meta.query_advice(w, Rotation::cur());
            let y = meta.query_advice(y, Rotation::cur());
            let row = zs
                .iter()
                .enumerate()
                .map(|(i, zi)| zi.clone() * pow(5, i as u32 + 1))
                .reduce(|acc, term| acc + term)
                .expect("seven limbs");
            Constraints::with_selector(
                selectors[8],
                vec![(
                    "row",
                    x0 * row - w + y * Expression::Constant(Fq::from(17u64)),
                )],
            )
        });
        meta.create_gate("g10 main instance", |meta| {
            let (a, b, c, d, public) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::cur()),
                meta.query_advice(d, Rotation::cur()),
                meta.query_instance(public, Rotation::cur()),
            );
            Constraints::without_selector(vec![("main pi", (a * c - b * d) * public)])
        });
        meta.create_gate("g11 main sum product", |meta| {
            let (a, b, c, d) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::cur()),
                meta.query_advice(c, Rotation::cur()),
                meta.query_advice(d, Rotation::cur()),
            );
            let f = meta.query_fixed(f, Rotation::cur());
            Constraints::without_selector(vec![(
                "main sp",
                f * ((a + b) * (c + d) - Expression::Constant(Fq::from(3u64))),
            )])
        });
        meta.create_gate("g12 two polys", |meta| {
            let (a, b, c) = (
                meta.query_advice(a, Rotation::cur()),
                meta.query_advice(b, Rotation::next()),
                meta.query_advice(c, Rotation::cur()),
            );
            Constraints::with_selector(
                selectors[0],
                vec![("sq", a.clone() * a.clone() - c.clone()), ("neg", -(b + c))],
            )
        });
        meta.lookup_any("listing lookup", Some(lookup_selector), |meta| {
            vec![(
                meta.query_advice(a, Rotation::cur()),
                meta.query_fixed(table, Rotation::cur()),
            )]
        });
        meta.create_gate("trash gate", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            Constraints::with_additive_selector(trash_selector, vec![("trash", b - a)])
        });

        ListingConfig {
            a,
            b,
            c,
            d,
            x,
            z,
            y,
            w,
            f,
            table,
            selectors,
            lookup_selector,
            trash_selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        layouter.assign_region(
            || "listing rows",
            |mut region| {
                for selector in &config.selectors {
                    selector.enable(&mut region, 1)?;
                }
                config.lookup_selector.enable(&mut region, 1)?;
                config.trash_selector.enable(&mut region, 1)?;
                region.assign_fixed(|| "f", config.f, 1, || Value::known(Fq::ONE))?;
                region.assign_fixed(|| "t", config.table, 1, || Value::known(Fq::ONE))?;
                for column in [config.a, config.b, config.c, config.d, config.y, config.w]
                    .into_iter()
                    .chain(config.x)
                    .chain(config.z)
                {
                    for row in 0..3 {
                        region.assign_advice(|| "v", column, row, || Value::known(Fq::ONE))?;
                    }
                }
                let cell =
                    region.assign_advice(|| "copy", config.a, 3, || Value::known(Fq::ONE))?;
                cell.copy_advice(|| "copy", &mut region, config.b, 4)?;
                Ok(())
            },
        )
    }
}

/// Parameters and VK for the listing test circuit.
fn listing_vk() -> (
    ParamsKZG<Bls12>,
    VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>,
) {
    let mut rng = ChaCha8Rng::seed_from_u64(0x11571);
    let params = ParamsKZG::<Bls12>::unsafe_setup(7, &mut rng);
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &ListingCircuit, 7)
        .expect("listing test circuit VK");
    (params, vk)
}

/// Render the listing test circuit with a separate VK.
fn render_listing_circuit() -> crate::RenderedArtifacts {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("render with listing")
}

#[test]
fn listing_and_manifest_are_emitted_and_self_consistent() {
    let artifacts = render_listing_circuit();
    let listing = artifacts.quotient_listing.clone().expect("listing emitted by default");
    let manifest = artifacts.quotient_manifest.clone().expect("manifest emitted by default");
    if let Ok(dir) = std::env::var("QUOTIENT_LISTING_TEST_DUMP") {
        std::fs::create_dir_all(&dir).ok();
        std::fs::write(format!("{dir}/QuotientListing.txt"), &listing).ok();
        std::fs::write(format!("{dir}/QuotientManifest.json"), &manifest).ok();
        std::fs::write(format!("{dir}/Halo2Verifier.sol"), &artifacts.verifier).ok();
        if let Some(vk) = &artifacts.verifying_key {
            std::fs::write(format!("{dir}/Halo2VerifyingKey.sol"), vk).ok();
        }
    }
    assert!(listing.starts_with("QUOTIENT VM LISTING"));
    assert!(listing.contains("[ok] program bytes and constant words read back from the VK payload"));
    assert!(listing.contains("exactly once"));
    assert!(manifest.contains("\"format\": \"halo2_solidity_verifier/quotient-vm-manifest\""));
    assert!(!extract_program_blocks(&listing).is_empty());
    // Every opcode family of interest shows up in this circuit's program.
    for needle in [
        "FOLD_SELECTOR",
        "FOLD_MAIN",
        "NATIVE_PERMUTATION",
        "NATIVE_LOOKUP",
    ] {
        assert!(listing.contains(needle), "listing should contain {needle}");
    }
}

#[test]
fn listing_does_not_change_the_rendered_solidity() {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    for options in [
        RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        },
        RenderOptions::default(),
    ] {
        let with = generator.render_with_listing(options, true).expect("with listing");
        let without = generator.render_with_listing(options, false).expect("without listing");
        assert_eq!(with.verifier, without.verifier);
        assert_eq!(with.verifying_key, without.verifying_key);
        assert!(with.quotient_listing.is_some() && with.quotient_manifest.is_some());
        assert!(without.quotient_listing.is_none() && without.quotient_manifest.is_none());
        assert_eq!(with, generator.render(options).expect("render"));
    }
}

/// Render the listing from a plan after applying `mutate` to it.
fn listing_after(
    mutate: impl FnOnce(&mut crate::lowering::plan::LoweringPlan),
) -> Result<super::QuotientListingArtifacts, String> {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let inputs = generator.inputs();
    let mut plan = inputs.lowering_plan();
    mutate(&mut plan);
    inputs.quotient_listing_artifacts(
        &plan,
        QuotientListingContext {
            separate_vk: true,
            external_quotient: false,
            trace: false,
        },
    )
}

/// Overwrite byte `byte` of the packed program both in the VK payload and in
/// the build (so the payload/build cross-check passes and the translation
/// validation is what must catch the change).
fn corrupt_program_byte(plan: &mut crate::lowering::plan::LoweringPlan, byte: usize, value: u8) {
    plan.quotient.build.bytes[byte] = value;
    let offset = plan.vk.quotient_program_offset_words.expect("program") + byte / 32;
    let mut word = plan.vk.constants[offset].1.to_be_bytes::<32>();
    word[byte % 32] = value;
    plan.vk.constants[offset].1 = U256::from_be_bytes(word);
}

/// First VM identity item of the unmodified plan, with its identity index.
fn first_vm_item() -> (
    usize,
    crate::lowering::quotient_numerator::vm::disasm::VmItem,
    Vec<U256>,
) {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let plan = generator.inputs().lowering_plan();
    let items = split_vm_items(&decode_vm_program(&plan.quotient.build.bytes).unwrap()).unwrap();
    let (item, planned) = items
        .into_iter()
        .zip(&plan.quotient.plan.items)
        .find(|(item, _)| item.kind == VmItemKind::Identity)
        .expect("test circuit has a VM identity");
    let j = match planned {
        crate::lowering::quotient_numerator::vm::QuotientProgramItem::Identity(identity) => {
            identity.meta.global_index
        }
        _ => unreachable!(),
    };
    (j, item, plan.quotient.build.consts.clone())
}

#[test]
fn listing_validation_rejects_corrupted_program_byte_naming_the_identity() {
    let (j, item, _) = first_vm_item();
    // Re-point the first memory operand of the identity to another published
    // slot: the program still decodes, but computes a different polynomial.
    let instruction = item
        .body()
        .iter()
        .find(|instruction| {
            matches!(
                instruction.opcode,
                Q_OP_PUSH_MEM_U16 | Q_OP_ADD_MEM_U16 | Q_OP_MUL_MEM_U16
            )
        })
        .expect("VM identity with a u16 memory operand");
    let pos = instruction.offset + 2;
    let err = listing_after(|plan| {
        let original = plan.quotient.build.bytes[pos];
        corrupt_program_byte(plan, pos, original.wrapping_add(0x20));
    })
    .expect_err("corrupted program byte must fail validation");
    assert!(
        err.contains(&format!("identity j={j} ")),
        "error should name j={j}: {err}"
    );
    assert!(err.contains("quotient listing validation failed"), "{err}");
}

#[test]
fn listing_validation_rejects_corrupted_constant_naming_the_identity() {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let plan = generator.inputs().lowering_plan();
    let items = split_vm_items(&decode_vm_program(&plan.quotient.build.bytes).unwrap()).unwrap();
    // Pick a constant used by exactly the VM identities and not by
    // anything else checked earlier: the first constant referenced by the
    // first VM identity.
    let (j, item) = items
        .iter()
        .zip(&plan.quotient.plan.items)
        .find_map(|(item, planned)| match planned {
            crate::lowering::quotient_numerator::vm::QuotientProgramItem::Identity(identity)
                if item.body().iter().any(|i| {
                    !crate::lowering::quotient_numerator::vm::disasm::vm_constant_refs(&i.op)
                        .is_empty()
                }) =>
            {
                Some((identity.meta.global_index, item.clone()))
            }
            _ => None,
        })
        .expect("VM identity using a constant");
    let slot = item
        .body()
        .iter()
        .flat_map(|i| crate::lowering::quotient_numerator::vm::disasm::vm_constant_refs(&i.op))
        .next()
        .unwrap() as usize;
    let err = listing_after(|plan| {
        let bumped = plan.quotient.build.consts[slot] + U256::from(1u64);
        plan.quotient.build.consts[slot] = bumped;
        let offset = plan.vk.quotient_const_offset_words.expect("consts") + slot;
        plan.vk.constants[offset].1 = bumped;
    })
    .expect_err("corrupted constant must fail validation");
    assert!(
        err.contains("quotient listing validation failed for identity j="),
        "{err}"
    );
    // The first VM identity that uses the constant is reported (identities
    // are validated in program order, so it is `j` or an earlier one that
    // shares the slot).
    let reported = err
        .split("identity j=")
        .nth(1)
        .and_then(|rest| rest.split(' ').next())
        .and_then(|n| n.parse::<usize>().ok())
        .expect("reported identity index");
    assert!(
        reported <= j,
        "reported j={reported} should not be after j={j}: {err}"
    );
}

#[test]
fn listing_rejects_payload_that_differs_from_build() {
    let err = listing_after(|plan| {
        let offset = plan.vk.quotient_program_offset_words.expect("program");
        plan.vk.constants[offset].1 ^= U256::from(1u64) << 200;
    })
    .expect_err("payload/build drift must fail");
    assert!(err.contains("differ"), "{err}");
}

#[test]
fn listing_rejects_invalid_opcode() {
    let (_, item, _) = first_vm_item();
    let err = listing_after(|plan| corrupt_program_byte(plan, item.byte_start(), 0x1a))
        .expect_err("reserved opcode must fail");
    assert!(err.contains("unknown quotient VM opcode 0x1a"), "{err}");
}

#[test]
fn listing_blocks_match_standalone_regeneration() {
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .unwrap();
    let listing = artifacts.quotient_listing.unwrap();
    let plan = generator.inputs().lowering_plan();
    let (slots, tokens) = super::build_slots(&plan.meta, &plan.data, &plan.memory).expect("slots");
    let symbols = ListingSymbols {
        slots: slots.iter().map(|s| (s.addr, s.name.clone())).collect(),
        tokens,
    };
    let items = split_vm_items(&decode_vm_program(&plan.quotient.build.bytes).unwrap()).unwrap();
    let qplan = &plan.quotient.plan;
    let item_identities = qplan
        .items
        .iter()
        .map(|item| match item {
            crate::lowering::quotient_numerator::vm::QuotientProgramItem::Identity(identity) => {
                vec![identity.meta.global_index]
            }
            crate::lowering::quotient_numerator::vm::QuotientProgramItem::NativeIdentity(k) => {
                vec![qplan.native_identities[*k].meta.global_index]
            }
            crate::lowering::quotient_numerator::vm::QuotientProgramItem::NativePermutation => {
                qplan
                    .native_permutation_identities
                    .iter()
                    .map(|i| i.meta.global_index)
                    .collect()
            }
            crate::lowering::quotient_numerator::vm::QuotientProgramItem::NativeLookup => {
                qplan.native_lookup_identities.iter().map(|i| i.meta.global_index).collect()
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(items.len(), item_identities.len());
    let blocks = render_program_blocks(
        &plan.quotient.build.bytes,
        &plan.quotient.build.consts,
        plan.quotient.program.program_mptr as u32,
        &symbols,
        &item_identities,
    )
    .unwrap();
    let shipped = extract_program_blocks(&listing);
    assert_eq!(
        shipped,
        blocks.iter().map(|b| b.text.clone()).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Decoder / interpreter against hand-assembled programs and the builder.
// ---------------------------------------------------------------------------

/// Numeric values over a plain memory map.
struct TestValues<'a> {
    consts: &'a [Fq],
    mem: &'a BTreeMap<u32, Fq>,
    tokens: &'a BTreeMap<u8, u32>,
}

impl VmValues for TestValues<'_> {
    type Value = Fq;
    fn zero(&self) -> Fq {
        Fq::ZERO
    }
    fn constant(&self, slot: u16) -> Result<Fq, String> {
        self.consts.get(slot as usize).copied().ok_or_else(|| "slot".to_string())
    }
    fn load(&self, addr: u32) -> Result<Fq, String> {
        self.mem.get(&addr).copied().ok_or_else(|| format!("unmapped {addr:#x}"))
    }
    fn token_addr(&self, token: u8) -> Result<u32, String> {
        self.tokens.get(&token).copied().ok_or_else(|| "token".to_string())
    }
    fn add(&self, a: Fq, b: Fq) -> Result<Fq, String> {
        Ok(a + b)
    }
    fn mul(&self, a: Fq, b: Fq) -> Result<Fq, String> {
        Ok(a * b)
    }
    fn neg(&self, a: Fq) -> Result<Fq, String> {
        Ok(-a)
    }
}

/// Memory map with 64 slots at 0x1000 + 32*i and token 0x09 at 0x2000.
fn test_memory(seed: u64) -> (BTreeMap<u32, Fq>, BTreeMap<u8, u32>) {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut mem = BTreeMap::new();
    for i in 0..64u32 {
        mem.insert(0x1000 + 0x20 * i, Fq::random(&mut rng));
    }
    mem.insert(0x2000, Fq::random(&mut rng));
    mem.insert(0x2040, Fq::random(&mut rng));
    mem.insert(0x0001_1000, Fq::random(&mut rng));
    let mut tokens = BTreeMap::new();
    tokens.insert(0x09u8, 0x2000u32);
    (mem, tokens)
}

/// Slot address helper.
fn slot(i: u32) -> u32 {
    0x1000 + 0x20 * i
}

/// Big-endian `u16` bytes.
fn be16(v: u32) -> [u8; 2] {
    (v as u16).to_be_bytes()
}

#[test]
fn decoder_covers_every_opcode_of_the_abi() {
    let consts = [3u64, 5, 7, 11].map(|c| fe_to_u256::<Fq>(&Fq::from(c))).to_vec();
    let cf = consts.iter().map(|c| super::blocks::consts_to_fr(&[*c])[0]).collect::<Vec<_>>();
    let (mem, tokens) = test_memory(7);
    let m = |i: u32| mem[&slot(i)];
    let mut program = Vec::new();
    let mut expected = Vec::new();

    // 1: PUSH_CONST (wide) + PUSH_MEM_LITERAL + ADD + FOLD_MAIN.
    program.push(Q_OP_PUSH_CONST);
    program.extend(be16(1));
    program.push(Q_OP_PUSH_MEM_LITERAL);
    program.extend(0x0001_1000u32.to_be_bytes());
    program.push(Q_OP_ADD);
    program.push(Q_OP_FOLD_MAIN);
    expected.push(cf[1] + mem[&0x0001_1000]);
    // 2: PUSH_MEM_TOKEN, PUSH_MEM_TOKEN_OFFSET, MUL, NEG, POW5, FOLD_SELECTOR.
    program.extend([Q_OP_PUSH_MEM_TOKEN, 0x09, Q_OP_PUSH_MEM_TOKEN_OFFSET, 0x09]);
    program.extend(0x40u32.to_be_bytes());
    program.extend([
        Q_OP_MUL,
        Q_OP_NEG,
        Q_OP_POW5,
        Q_OP_FOLD_SELECTOR,
        0x02,
        0x00,
        0x03,
    ]);
    let v = -(mem[&0x2000] * mem[&0x2040]);
    expected.push(v * v * v * v * v);
    // 3: PUSH_CONST_U8, ADD/MUL const (u8 and wide), ADD/MUL mem, fused ops.
    program.extend([
        Q_OP_PUSH_CONST_U8,
        0,
        Q_OP_ADD_CONST_U8,
        1,
        Q_OP_MUL_CONST_U8,
        2,
    ]);
    program.push(Q_OP_ADD_CONST);
    program.extend(be16(3));
    program.push(Q_OP_MUL_CONST);
    program.extend(be16(0));
    program.push(Q_OP_ADD_MEM_U16);
    program.extend(be16(slot(0)));
    program.push(Q_OP_MUL_MEM_U16);
    program.extend(be16(slot(1)));
    program.push(Q_OP_ADD_MUL_MEM_MEM_CONST_U8);
    program.extend(be16(slot(2)));
    program.extend(be16(slot(3)));
    program.push(1);
    program.push(Q_OP_ADD_MUL_CONST_U8_MEM_U16);
    program.extend(be16(slot(4)));
    program.push(2);
    program.push(Q_OP_ADD_MUL_MEM_MEM);
    program.extend(be16(slot(5)));
    program.extend(be16(slot(6)));
    program.push(Q_OP_FOLD_MAIN);
    let mut acc = (((cf[0] + cf[1]) * cf[2] + cf[3]) * cf[0] + m(0)) * m(1);
    acc += m(2) * m(3) * cf[1];
    acc += m(4) * cf[2];
    acc += m(5) * m(6);
    expected.push(acc);
    // 4: runs and AFFINE_SUM.
    program.push(Q_OP_PUSH_MEM_U16);
    program.extend(be16(slot(7)));
    program.push(Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8);
    program.extend(be16(2));
    for (l, r, c) in [(8, 9, 0u8), (10, 11, 3)] {
        program.extend(be16(slot(l)));
        program.extend(be16(slot(r)));
        program.push(c);
    }
    program.push(Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16);
    program.extend(be16(2));
    for (p, c) in [(12, 1u8), (13, 2)] {
        program.extend(be16(slot(p)));
        program.push(c);
    }
    program.push(Q_OP_AFFINE_SUM);
    program.extend(be16(1));
    program.extend(be16(1));
    program.extend(be16(slot(14)));
    program.push(3);
    program.extend(be16(slot(15)));
    program.extend(be16(slot(16)));
    program.push(0);
    program.push(Q_OP_FOLD_MAIN);
    expected.push(
        m(7) + m(8) * m(9) * cf[0]
            + m(10) * m(11) * cf[3]
            + m(12) * cf[1]
            + m(13) * cf[2]
            + m(14) * cf[3]
            + m(15) * m(16) * cf[0],
    );
    // 5: LIN7 + BILIN7_ROW + BILIN7_PAIRWISE, ADD, ADD, FOLD_MAIN.
    program.push(Q_OP_LIN7);
    let mut lin = Fq::ZERO;
    for i in 0..7u32 {
        program.push((i % 4) as u8);
        program.extend(be16(slot(20 + i)));
        lin += cf[(i % 4) as usize] * m(20 + i);
    }
    program.push(Q_OP_BILIN7_ROW);
    program.extend(be16(slot(0)));
    let mut row = Fq::ZERO;
    for i in 0..7u32 {
        program.push(((i + 1) % 4) as u8);
        program.extend(be16(slot(30 + i)));
        row += m(0) * m(30 + i) * cf[((i + 1) % 4) as usize];
    }
    program.push(Q_OP_BILIN7_PAIRWISE);
    program.extend(be16(slot(20)));
    program.extend(be16(slot(30)));
    let mut pair = Fq::ZERO;
    for k in 0..13u32 {
        program.push((k % 4) as u8);
    }
    for i in 0..7u32 {
        for j in 0..7u32 {
            pair += m(20 + i) * m(30 + j) * cf[((i + j) % 4) as usize];
        }
    }
    program.extend([Q_OP_ADD, Q_OP_ADD, Q_OP_FOLD_MAIN]);
    expected.push(lin + row + pair);
    // 6: MODARITH7 with every block kind.
    program.extend([Q_OP_MODARITH7, 0x03]);
    program.extend(be16(slot(40)));
    program.push(2); // constant seed
    program.extend([1, 1, 1, 1, 1]);
    let mut modarith = cf[2];
    for i in 0..7u32 {
        program.push(1);
        program.extend(be16(slot(20 + i)));
        modarith += cf[1] * m(20 + i);
    }
    program.extend(be16(slot(41)));
    for i in 0..7u32 {
        program.push(3);
        program.extend(be16(slot(30 + i)));
        modarith += m(41) * m(30 + i) * cf[3];
    }
    program.extend(be16(slot(20)));
    program.extend(be16(slot(30)));
    program.extend([0u8; 13]);
    for i in 0..7u32 {
        for j in 0..7u32 {
            modarith += m(20 + i) * m(30 + j) * cf[0];
        }
    }
    program.push(2);
    program.extend(be16(slot(42)));
    modarith += cf[2] * m(42);
    program.push(1);
    program.extend(be16(slot(43)));
    program.extend(be16(slot(44)));
    modarith += cf[1] * m(43) * m(44);
    program.push(Q_OP_FOLD_MAIN);
    expected.push(modarith * m(40));
    // Native markers at identity boundaries.
    program.extend([
        Q_OP_NATIVE_PERMUTATION,
        Q_OP_NATIVE_LOOKUP,
        Q_OP_NATIVE_IDENTITY,
        0,
        1,
    ]);

    let instructions = decode_vm_program(&program).expect("hand-assembled program decodes");
    let used = instructions.iter().map(|i| i.opcode).collect::<std::collections::BTreeSet<_>>();
    for spec in QUOTIENT_OPCODE_TABLE {
        assert!(
            used.contains(&spec.opcode),
            "opcode {} not exercised",
            spec.name
        );
    }
    assert_eq!(used.len(), QUOTIENT_OPCODE_TABLE.len(), "31 opcodes");
    // Decoder lengths agree with the builder's walker.
    let builder_walk = quotient_bytecode_ops(&program).collect::<Vec<_>>();
    let decoder_walk = instructions.iter().map(|i| (i.offset, i.opcode, i.len)).collect::<Vec<_>>();
    assert_eq!(builder_walk, decoder_walk);
    let items = split_vm_items(&instructions).expect("stack discipline");
    let identities = items.iter().filter(|i| i.kind == VmItemKind::Identity).collect::<Vec<_>>();
    assert_eq!(identities.len(), expected.len());
    let values = TestValues {
        consts: &cf,
        mem: &mem,
        tokens: &tokens,
    };
    for (item, expected) in identities.iter().zip(&expected) {
        assert_eq!(&eval_vm_identity(item.body(), &values).unwrap(), expected);
    }
    // Symbolic expansion agrees with the numeric evaluation.
    let symbolic = super::blocks::SymbolicValues {
        consts: &cf,
        tokens: &tokens,
    };
    for (item, expected) in identities.iter().zip(&expected) {
        let poly = eval_vm_identity(item.body(), &symbolic).unwrap();
        assert_eq!(&eval_poly(&poly, &mem), expected);
    }
    // The shared renderer tiles every byte.
    let mut symbols = ListingSymbols::default();
    for addr in mem.keys() {
        symbols.slots.insert(*addr, format!("s{addr:x}"));
    }
    symbols.tokens.insert(0x09, ("INSTANCE_EVAL_MPTR".to_string(), 0x2000));
    let mut item_identities = Vec::new();
    let mut j = 0usize;
    for item in &items {
        let n = if matches!(
            item.kind,
            VmItemKind::NativePermutation | VmItemKind::NativeLookup
        ) {
            2
        } else {
            1
        };
        item_identities.push((j..j + n).collect());
        j += n;
    }
    let blocks = render_program_blocks(&program, &consts, 0x4000, &symbols, &item_identities)
        .expect("render");
    assert_eq!(blocks.len(), items.len());
}

/// Evaluate a polynomial over a memory map.
fn eval_poly(poly: &Poly, mem: &BTreeMap<u32, Fq>) -> Fq {
    poly.terms()
        .map(|(monomial, coeff)| monomial.iter().fold(*coeff, |acc, addr| acc * mem[addr]))
        .fold(Fq::ZERO, |acc, term| acc + term)
}

/// Random expression over slots 0..48 and small constants.
fn random_expr(rng: &mut ChaCha8Rng, depth: usize) -> QuotientExpr {
    if depth == 0 || rng.gen_range(0..4) == 0 {
        return if rng.gen_bool(0.3) {
            QuotientExpr::Const(fe_to_u256::<Fq>(&Fq::from(rng.gen_range(1..20u64))))
        } else {
            QuotientExpr::Mem(QuotientMem::Literal(slot(rng.gen_range(0..48))))
        };
    }
    match rng.gen_range(0..3) {
        0 => QuotientExpr::Add(
            Box::new(random_expr(rng, depth - 1)),
            Box::new(random_expr(rng, depth - 1)),
        ),
        1 => QuotientExpr::Mul(
            Box::new(random_expr(rng, depth - 1)),
            Box::new(random_expr(rng, depth - 1)),
        ),
        _ => QuotientExpr::Neg(Box::new(random_expr(rng, depth - 1))),
    }
}

/// Seven-limb linear expression `sum c_i * slot(base + i)`.
fn limb_sum(base: u32, coeff: impl Fn(u32) -> u64) -> QuotientExpr {
    (0..7u32)
        .map(|i| {
            QuotientExpr::Mul(
                Box::new(QuotientExpr::Const(fe_to_u256::<Fq>(&Fq::from(coeff(i))))),
                Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(base + i)))),
            )
        })
        .reduce(|a, b| QuotientExpr::Add(Box::new(a), Box::new(b)))
        .unwrap()
}

#[test]
fn decoder_matches_builder_after_run_compaction() {
    let mut rng = ChaCha8Rng::seed_from_u64(0xd15a55);
    let mut exprs = (0..40).map(|_| random_expr(&mut rng, 5)).collect::<Vec<_>>();
    // Shapes that trigger compaction and limb opcodes.
    let affine = (0..6u32)
        .map(|i| {
            QuotientExpr::Mul(
                Box::new(QuotientExpr::Mul(
                    Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(i)))),
                    Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(i + 1)))),
                )),
                Box::new(QuotientExpr::Const(fe_to_u256::<Fq>(&Fq::from(
                    3 + i as u64,
                )))),
            )
        })
        .chain((0..5u32).map(|i| {
            QuotientExpr::Mul(
                Box::new(QuotientExpr::Const(fe_to_u256::<Fq>(&Fq::from(
                    9 + i as u64,
                )))),
                Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(10 + i)))),
            )
        }))
        .reduce(|a, b| QuotientExpr::Add(Box::new(a), Box::new(b)))
        .unwrap();
    exprs.push(QuotientExpr::Add(
        Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(20)))),
        Box::new(affine),
    ));
    exprs.push(limb_sum(20, |i| 1 << (8 * i)));
    exprs.push(QuotientExpr::Add(
        Box::new(limb_sum(20, |i| 3 + i as u64)),
        Box::new(QuotientExpr::Mem(QuotientMem::Literal(slot(40)))),
    ));
    let mut builder = QuotientProgramBuilder::default();
    for (idx, expr) in exprs.iter().enumerate() {
        let target = if idx % 3 == 0 {
            QuotientTarget::Selector(idx % 2)
        } else {
            QuotientTarget::Main
        };
        let gap = matches!(target, QuotientTarget::Selector(_)).then_some(idx % 5);
        builder.identity_expr(expr, target, gap);
    }
    let build = builder.finish();
    let consts = super::blocks::consts_to_fr(&build.consts);
    let instructions = decode_vm_program(&build.bytes).expect("decode compacted program");
    let items = split_vm_items(&instructions).expect("split");
    assert_eq!(items.len(), exprs.len());
    let compacted = instructions.iter().any(|i| {
        matches!(
            i.opcode,
            Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 | Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 | Q_OP_AFFINE_SUM
        )
    });
    assert!(
        compacted,
        "test program should contain run/affine compaction"
    );
    assert!(
        instructions.iter().any(|i| matches!(i.opcode, Q_OP_LIN7 | Q_OP_MODARITH7)),
        "test program should contain limb opcodes"
    );
    for seed in 0..4 {
        let (mem, tokens) = test_memory(100 + seed);
        let values = TestValues {
            consts: &consts,
            mem: &mem,
            tokens: &tokens,
        };
        for (item, expr) in items.iter().zip(&exprs) {
            let vm = eval_vm_identity(item.body(), &values).unwrap();
            let direct = eval_quotient_expr(
                expr,
                &tokens,
                &|c| Ok(c),
                &|a| mem.get(&a).copied().ok_or_else(|| "mem".to_string()),
                &|a, b| Ok(a + b),
                &|a, b| Ok(a * b),
                &|a| Ok(-a),
            )
            .unwrap();
            assert_eq!(vm, direct);
        }
    }
}

#[test]
fn pointer_relocation_round_trips_and_preserves_structure() {
    let (_, item, _) = first_vm_item();
    let (params, vk) = listing_vk();
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let plan = generator.inputs().lowering_plan();
    let program = &plan.quotient.build.bytes;
    let (moved, count) = relocate_vm_pointers(program, 0x100, 0x20).unwrap();
    assert!(count > 0);
    assert_ne!(&moved, program);
    let (back, count_back) = relocate_vm_pointers(&moved, 0x120, -0x20).unwrap();
    assert_eq!(count, count_back);
    assert_eq!(&back, program);
    let _ = item;
}

#[test]
fn readable_constants_use_short_forms() {
    use super::poly::readable_fr;
    assert_eq!(readable_fr(Fq::ONE), "1");
    assert_eq!(readable_fr(-Fq::ONE), "-1");
    assert_eq!(readable_fr(Fq::from(1u64 << 56)), "2^56");
    assert_eq!(readable_fr(-Fq::from(1u64 << 56)), "-2^56");
    assert_eq!(readable_fr(Fq::from(6u64 << 56)), "3*2^57");
    assert_eq!(readable_fr(Fq::from(4096u64)), "2^12");
    assert_eq!(readable_fr(Fq::from(13u64)), "13");
    let big = Fq::from_str_vartime("123456789012345678901234567890").unwrap();
    assert!(readable_fr(big).starts_with("0x"));
    assert!(readable_fr(-big).starts_with("r - 0x"));
}

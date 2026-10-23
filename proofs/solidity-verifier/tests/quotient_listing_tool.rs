//! Round-trip tests for the `quotient_listing` auditor example.
//!
//! Renders a small circuit (no SRS or solc needed), writes the verifier, VK,
//! listing and manifest to a temporary directory, and runs the example's
//! checks against them: an exact round trip, a VK whose payload has one extra
//! header word (the shape of the production Nightfall VKs), and corrupted
//! inputs that must be rejected.

use std::{fs, path::PathBuf};

use ff::Field;
use halo2_solidity_verifier::{
    quotient_listing::relocate_program_pointers, GeneratorConfig, RenderOptions, RenderVk,
    SolidityGenerator,
};
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Constraints,
        Error as PlonkError, Expression, Fixed, Selector,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

#[path = "../examples/quotient_listing.rs"]
#[allow(dead_code)]
mod tool;

#[derive(Clone, Debug)]
struct ToolConfig {
    adv: [Column<Advice>; 4],
    fixed: Column<Fixed>,
    table: Column<Fixed>,
    selectors: Vec<Selector>,
    lookup: Selector,
}

#[derive(Clone, Debug, Default)]
struct ToolCircuit;

impl Circuit<Fq> for ToolCircuit {
    type Config = ToolConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> ToolConfig {
        let adv = std::array::from_fn(|_| meta.advice_column());
        let fixed = meta.fixed_column();
        let table = meta.fixed_column();
        let _committed = meta.instance_column();
        let public = meta.instance_column();
        meta.enable_equality(adv[0]);
        meta.enable_equality(adv[1]);
        let selectors = (0..8).map(|_| meta.selector()).collect::<Vec<_>>();
        let lookup = meta.complex_selector();
        let k = |v: u64| Expression::Constant(Fq::from(v));
        for (idx, selector) in selectors.iter().enumerate() {
            meta.create_gate("tool gate", |meta| {
                let f = meta.query_fixed(fixed, Rotation::cur());
                let mut q = |c: usize, r: i32| meta.query_advice(adv[c % 4], Rotation(r));
                let v = idx as u64 + 2;
                let (a, b, c, d) = (q(0, 0), q(1, 0), q(2, 0), q(3, 1));
                let (x, y, z) = (q(idx, 0), q(idx + 1, 0), q(idx + 2, 0));
                let polys = vec![
                    ("affine", a * b * k(v) + c * k(v + 1) - d),
                    ("fixed", f * x + y * z - k(v * v)),
                ];
                Constraints::with_selector(*selector, polys)
            });
        }
        meta.create_gate("tool main", |meta| {
            let a = meta.query_advice(adv[0], Rotation::cur());
            let b = meta.query_advice(adv[1], Rotation::prev());
            let p = meta.query_instance(public, Rotation::cur());
            Constraints::without_selector(vec![("main", (a.clone() - b) * a * p)])
        });
        meta.lookup_any("tool lookup", Some(lookup), |meta| {
            vec![(
                meta.query_advice(adv[2], Rotation::cur()),
                meta.query_fixed(table, Rotation::cur()),
            )]
        });
        ToolConfig {
            adv,
            fixed,
            table,
            selectors,
            lookup,
        }
    }

    fn synthesize(
        &self,
        config: ToolConfig,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), PlonkError> {
        layouter.assign_region(
            || "tool rows",
            |mut region| {
                for selector in &config.selectors {
                    selector.enable(&mut region, 1)?;
                }
                config.lookup.enable(&mut region, 1)?;
                region.assign_fixed(|| "f", config.fixed, 1, || Value::known(Fq::ONE))?;
                region.assign_fixed(|| "t", config.table, 1, || Value::known(Fq::ONE))?;
                for column in config.adv {
                    for row in 0..3 {
                        region.assign_advice(|| "v", column, row, || Value::known(Fq::ONE))?;
                    }
                }
                let cell =
                    region.assign_advice(|| "c", config.adv[0], 3, || Value::known(Fq::ONE))?;
                cell.copy_advice(|| "c", &mut region, config.adv[1], 4)?;
                Ok(())
            },
        )
    }
}

/// Render the tool circuit and write its artifacts to a fresh directory.
fn render_to_dir(name: &str) -> PathBuf {
    let mut rng = ChaCha8Rng::seed_from_u64(99);
    let params = ParamsKZG::<Bls12>::unsafe_setup(6, &mut rng);
    let vk = keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(&params, &ToolCircuit, 6)
        .expect("vk");
    let generator = SolidityGenerator::new(&params, &vk, GeneratorConfig::new(1, 1));
    let artifacts = generator
        .render(RenderOptions {
            vk: RenderVk::Separate,
            ..RenderOptions::default()
        })
        .expect("render");
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("quotient-listing-{name}"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Halo2Verifier.sol"), &artifacts.verifier).unwrap();
    fs::write(
        dir.join("Halo2VerifyingKey.sol"),
        artifacts.verifying_key.unwrap(),
    )
    .unwrap();
    fs::write(
        dir.join("QuotientListing.txt"),
        artifacts.quotient_listing.unwrap(),
    )
    .unwrap();
    fs::write(
        dir.join("QuotientManifest.json"),
        artifacts.quotient_manifest.unwrap(),
    )
    .unwrap();
    dir
}

fn opts(dir: &std::path::Path, vk: &str, verifier: bool) -> tool::Options {
    tool::Options {
        vk: dir.join(vk).display().to_string(),
        manifest: dir.join("QuotientManifest.json").display().to_string(),
        listing: Some(dir.join("QuotientListing.txt").display().to_string()),
        verifier: verifier.then(|| dir.join("Halo2Verifier.sol").display().to_string()),
        evaluator: None,
        out: Some(dir.join("regenerated-blocks.txt").display().to_string()),
    }
}

#[test]
fn tool_round_trips_on_a_fresh_render() {
    let dir = render_to_dir("exact");
    let report = tool::check(&opts(&dir, "Halo2VerifyingKey.sol", true)).expect("tool runs");
    assert_eq!(report.failures, 0, "{}", report.lines.join("\n"));
    assert_eq!(report.delta_words, 0);
    assert_eq!(report.status(), 0);
    assert!(report.lines.iter().any(|l| l.contains("identical to the shipped listing")));
    assert!(report
        .lines
        .iter()
        .any(|l| l.contains("verifier pins EXPECTED_VK_CODEHASH_WORD")));

    // The same check from the deployed runtime given as hex.
    let manifest: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("QuotientManifest.json")).unwrap())
            .unwrap();
    let payload =
        tool::parse_vk_source(&fs::read_to_string(dir.join("Halo2VerifyingKey.sol")).unwrap())
            .unwrap();
    fs::write(
        dir.join("runtime.hex"),
        format!("0x{}", hex::encode(payload.runtime())),
    )
    .unwrap();
    let report = tool::check(&opts(&dir, "runtime.hex", true)).expect("tool runs on hex");
    assert_eq!(report.failures, 0, "{}", report.lines.join("\n"));
    assert_eq!(
        report
            .lines
            .iter()
            .filter(|l| l.contains("codehash equals the manifest"))
            .count(),
        1
    );
    assert!(manifest["program"]["length_bytes"].as_u64().unwrap() > 0);
    assert_eq!(
        tool::run(&[
            dir.join("Halo2VerifyingKey.sol").display().to_string(),
            dir.join("QuotientManifest.json").display().to_string(),
        ]),
        0
    );
}

#[test]
fn tool_accepts_a_one_word_header_shift_with_relocated_pointers() {
    // Build the payload a generator with one extra header word would emit:
    // insert a word at index 11, and move every VM memory pointer >= VK_MPTR
    // by +0x20 because everything after the VK moves by one word.
    let dir = render_to_dir("shift");
    let manifest: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("QuotientManifest.json")).unwrap())
            .unwrap();
    let vk_mptr = u32::from_str_radix(
        manifest["vk"]["vk_mptr"].as_str().unwrap().trim_start_matches("0x"),
        16,
    )
    .unwrap();
    let prog_off = manifest["program"]["vk_payload_word_offset"].as_u64().unwrap() as usize;
    let prog_len = manifest["program"]["length_bytes"].as_u64().unwrap() as usize;
    let payload =
        tool::parse_vk_source(&fs::read_to_string(dir.join("Halo2VerifyingKey.sol")).unwrap())
            .unwrap();
    let mut bytes = payload.bytes();
    let program = bytes[prog_off * 32..prog_off * 32 + prog_len].to_vec();
    let (moved, count) = relocate_program_pointers(&program, vk_mptr, 0x20).unwrap();
    assert!(count > 0);
    bytes[prog_off * 32..prog_off * 32 + prog_len].copy_from_slice(&moved);
    bytes.splice(11 * 32..11 * 32, [0xabu8; 32]);
    let mut runtime = vec![0xfe];
    runtime.extend(bytes);
    fs::write(dir.join("shifted.hex"), hex::encode(runtime)).unwrap();

    let mut options = opts(&dir, "shifted.hex", false);
    options.out = Some(dir.join("shifted-blocks.txt").display().to_string());
    let report = tool::check(&options).expect("tool runs");
    assert_eq!(report.failures, 0, "{}", report.lines.join("\n"));
    assert_eq!(report.delta_words, 1);
    assert_eq!(report.status(), 2);
    assert!(report
        .lines
        .iter()
        .any(|l| l.contains(&format!("all {count} memory-pointer operands"))));
    let shifted_blocks = fs::read_to_string(dir.join("shifted-blocks.txt")).unwrap();
    assert!(shifted_blocks.contains(">>> program"));
}

#[test]
fn tool_rejects_corrupted_program_listing_and_verifier() {
    let dir = render_to_dir("corrupt");
    let manifest: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("QuotientManifest.json")).unwrap())
            .unwrap();
    let vk_source = fs::read_to_string(dir.join("Halo2VerifyingKey.sol")).unwrap();

    // Flip one nibble in the first program word of the VK source.
    let prog_off = manifest["program"]["vk_payload_word_offset"].as_u64().unwrap();
    let needle = format!("mstore(add(payload, {:#06x}), 0x", prog_off * 32);
    let pos = vk_source.find(&needle).expect("program word line") + needle.len();
    let mut corrupted = vk_source.clone().into_bytes();
    corrupted[pos + 4] = if corrupted[pos + 4] == b'0' {
        b'1'
    } else {
        b'0'
    };
    fs::write(dir.join("CorruptVk.sol"), &corrupted).unwrap();
    let report = tool::check(&opts(&dir, "CorruptVk.sol", false)).expect("tool runs");
    assert!(report.failures > 0, "{}", report.lines.join("\n"));
    assert!(report
        .lines
        .iter()
        .any(|l| l.starts_with("[FAIL]")
            && (l.contains("program keccak256") || l.contains("decode"))));

    // Edit one instruction line inside a program block of the listing.
    let listing = fs::read_to_string(dir.join("QuotientListing.txt")).unwrap();
    let line = listing
        .lines()
        .skip_while(|l| !l.starts_with("  >>> program "))
        .nth(1)
        .expect("instruction line")
        .to_string();
    fs::write(
        dir.join("QuotientListing.txt"),
        listing.replacen(&line, &format!("{line} (edited)"), 1),
    )
    .unwrap();
    let report = tool::check(&opts(&dir, "Halo2VerifyingKey.sol", false)).expect("tool runs");
    assert_eq!(report.failures, 2, "{}", report.lines.join("\n"));
    assert!(report.lines.iter().any(|l| l.contains("first difference in block 0")));

    // A verifier that pins a different VK.
    fs::write(dir.join("QuotientListing.txt"), &listing).unwrap();
    let verifier = fs::read_to_string(dir.join("Halo2Verifier.sol")).unwrap();
    let codehash = manifest["vk"]["runtime_codehash"].as_str().unwrap();
    let other = format!("0x{}", "11".repeat(32));
    fs::write(
        dir.join("Halo2Verifier.sol"),
        verifier.replace(codehash, &other),
    )
    .unwrap();
    let report = tool::check(&opts(&dir, "Halo2VerifyingKey.sol", true)).expect("tool runs");
    assert_eq!(report.failures, 1, "{}", report.lines.join("\n"));
    assert!(report
        .lines
        .iter()
        .any(|l| l.starts_with("[FAIL] verifier pins EXPECTED_VK_CODEHASH_WORD")));
}

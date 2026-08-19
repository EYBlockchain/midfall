#![no_main]

use std::sync::LazyLock;

use halo2_solidity_verifier::{
    encode_calldata, GeneratorConfig, SolidityGenerator, FN_SIG_VERIFY_PROOF,
};
use libfuzzer_sys::fuzz_target;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        keygen_vk_with_k, Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Selector,
    },
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        Rotation,
    },
};
use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};

const K: u32 = 5;

struct FuzzFixture {
    generator: SolidityGenerator<'static>,
}

static FIXTURE: LazyLock<FuzzFixture> = LazyLock::new(|| {
    let mut rng = ChaCha8Rng::seed_from_u64(0xf00d_f077);
    let params = Box::leak(Box::new(ParamsKZG::<Bls12>::unsafe_setup(K, &mut rng)));
    let circuit = MiniCircuit::default();
    let vk = Box::leak(Box::new(
        keygen_vk_with_k::<Fq, KZGCommitmentScheme<Bls12>, _>(params, &circuit, K)
            .expect("mini circuit VK generation"),
    ));
    FuzzFixture {
        generator: SolidityGenerator::new(params, vk, GeneratorConfig::new(1, 1)),
    }
});

#[derive(Clone, Debug, Default)]
struct MiniCircuit;

#[derive(Clone, Debug)]
struct MiniConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    out: Column<Advice>,
    selector: Selector,
}

impl Circuit<Fq> for MiniCircuit {
    type Config = MiniConfig;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self
    }

    fn params(&self) -> Self::Params {}

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let out = meta.advice_column();
        let committed_instance = meta.instance_column();
        let public_instance = meta.instance_column();
        let selector = meta.selector();

        meta.create_gate("mini public balance", |meta| {
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let out = meta.query_advice(out, Rotation::cur());
            let committed = meta.query_instance(committed_instance, Rotation::cur());
            let public = meta.query_instance(public_instance, Rotation::cur());

            Constraints::with_selector(
                selector,
                vec![("public balance", a + b + committed + public - out)],
            )
        });

        MiniConfig {
            a,
            b,
            out,
            selector,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mini witness",
            |mut region| {
                config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", config.a, 0, || Value::known(Fq::from(3)))?;
                region.assign_advice(|| "b", config.b, 0, || Value::known(Fq::from(4)))?;
                region.assign_advice(|| "out", config.out, 0, || Value::known(Fq::from(7)))?;
                Ok(())
            },
        )
    }
}

fuzz_target!(|compressed_proof: &[u8]| {
    if let Ok(proof) = FIXTURE.generator.repack_proof(compressed_proof) {
        assert_eq!(proof.len() % 32, 0, "repacked proof must be word-aligned");

        let calldata = encode_calldata(&proof, &[Fq::from(0)]);
        assert_eq!(&calldata[..4], FN_SIG_VERIFY_PROOF.as_slice());
        assert_eq!(
            calldata.len(),
            4 + 0x40 + 0x20 + proof.len() + 0x20 + 0x20,
            "single-instance calldata length should match ABI dynamic layout",
        );
    }
});

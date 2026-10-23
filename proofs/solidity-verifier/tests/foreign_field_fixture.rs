// SPDX-License-Identifier: CC0-1.0
//! Foreign-field / EC fixture for the direct quotient lowering.
//!
//! A small ZkStdLib circuit with the secp256k1 chips: a foreign-field
//! multiplication and addition (`Foreign-field multiplication` /
//! `normalization` gates) and EC doubling / addition (`Foreign-field EC ...`
//! gates). These gates are the shapes the direct lowering recognises
//! (`sum_exprs`, `pair_wise_prod` by degree, shifted limbs). The honest proof
//! is verified by Vm and Direct renders; with `rust-verifier-trace` the
//! Rust/Solidity trace (including the direct intermediates) is compared and
//! the emitted quotient Yul of both lowerings is compared with the Rust
//! reference on random evaluation frames (`tests/common::quotient_probe`).

#![cfg(feature = "evm")]

mod common;

use std::{env, path::Path};

use ff::Field;
use halo2_solidity_verifier::{
    compile_solidity, pinned_solc_available, CallOutcome, Evm, GeneratorConfig,
    QuotientIdentitySource, QuotientLowering, RenderOptions, RenderVk, SolidityGenerator,
};
use midnight_circuits::{
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, EccInstructions,
        PublicInputInstructions,
    },
    types::AssignedNative,
};
use midnight_curves::k256::{Fp as K256Base, K256};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
};
use midnight_zk_stdlib::{utils::plonk_api::srs_for_test, Relation, ZkStdLib, ZkStdLibArch};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use sha3::Keccak256;

type F = midnight_curves::Fq;

const RUN_EVM_TESTS_ENV: &str = "HALO2_SOLIDITY_RUN_EVM_TESTS";

#[derive(Clone, Default)]
struct ForeignFieldCircuit;

impl Relation for ForeignFieldCircuit {
    type Instance = F;
    type Witness = (F, K256Base, K256Base);

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let x: AssignedNative<F> = std_lib.assign(layouter, witness.map(|w| w.0))?;
        std_lib.constrain_as_public_input(layouter, &x)?;

        let curve = std_lib.secp256k1_curve();
        let base = curve.base_field_chip();
        let a = base.assign(layouter, witness.map(|w| w.1))?;
        let b = base.assign(layouter, witness.map(|w| w.2))?;
        let ab = base.mul(layouter, &a, &b, None)?;
        let sum = base.add(layouter, &ab, &a)?;
        let expected = base.assign(layouter, witness.map(|(_, a, b)| a * b + a))?;
        base.assert_equal(layouter, &sum, &expected)?;

        let g = curve.assign_fixed(layouter, K256::generator())?;
        let g2 = curve.double(layouter, &g)?;
        let _g3 = curve.add(layouter, &g2, &g)?;
        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            secp256k1: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ForeignFieldCircuit)
    }
}

fn srs_dir() -> String {
    env::var("SRS_DIR").unwrap_or_else(|_| {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../zk_stdlib/examples/assets"
        )
        .to_string()
    })
}

fn env_flag_enabled(name: &str) -> bool {
    env::var(name)
        .map(|value| matches!(value.as_str(), "1" | "true" | "TRUE" | "yes" | "YES"))
        .unwrap_or(false)
}

/// Proof material shared by the tests of this file (proved once).
struct Fixture {
    srs: midnight_proofs::poly::kzg::params::ParamsKZG<midnight_curves::Bls12>,
    vk: midnight_zk_stdlib::MidnightVK,
    proof: Vec<u8>,
    instance: F,
}

/// Prove the foreign-field circuit once; `None` when the EVM tier is not
/// enabled or no SRS is available.
fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: std::sync::OnceLock<Option<Fixture>> = std::sync::OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            if !env_flag_enabled(RUN_EVM_TESTS_ENV) {
                eprintln!(
                    "skipping foreign-field Solidity fixture: set {RUN_EVM_TESTS_ENV}=1 to run it"
                );
                return None;
            }
            let srs_dir = srs_dir();
            if !Path::new(&format!("{srs_dir}/bls_filecoin_2p19")).exists() {
                eprintln!("skipping foreign-field Solidity fixture: no SRS under {srs_dir}");
                return None;
            }
            env::set_var("SRS_DIR", &srs_dir);

            let relation = ForeignFieldCircuit;
            let srs = srs_for_test(&relation, None);
            let vk = midnight_zk_stdlib::setup_vk(&srs, &relation);
            let pk = midnight_zk_stdlib::setup_pk(&relation, &vk);
            let mut rng = ChaCha8Rng::seed_from_u64(0x00ff_00ff);
            let witness = (
                F::random(&mut rng),
                K256Base::random(&mut rng),
                K256Base::random(&mut rng),
            );
            let instance = witness.0;
            let proof = midnight_zk_stdlib::prove::<ForeignFieldCircuit, Keccak256>(
                &srs,
                &pk,
                &relation,
                &instance,
                witness,
                ChaCha8Rng::seed_from_u64(0x00ff_00fe),
            )
            .expect("foreign-field proof generation should not fail");
            midnight_zk_stdlib::verify::<ForeignFieldCircuit, Keccak256>(
                &srs.verifier_params(),
                &vk,
                &instance,
                None,
                &proof,
            )
            .expect("native verifier should accept the foreign-field proof");
            Some(Fixture {
                srs,
                vk,
                proof,
                instance,
            })
        })
        .as_ref()
}

fn generator(fx: &Fixture) -> SolidityGenerator<'_> {
    SolidityGenerator::new(&fx.srs, fx.vk.vk(), GeneratorConfig::new(1, 1))
}

#[test]
fn foreign_field_renders_and_verifies_in_both_lowerings() {
    let Some(fx) = fixture() else { return };
    let generator = generator(fx);
    let manifest = generator.quotient_identity_manifest();
    for gate in [
        "Foreign-field multiplication",
        "Foreign-field normalization",
        "Foreign-field EC lambda slope",
    ] {
        assert!(
            manifest.entries.iter().any(|e| matches!(
                &e.source,
                QuotientIdentitySource::Gate { gate_name, .. } if gate_name == gate
            )),
            "{gate} gate present"
        );
    }
    eprintln!(
        "[foreign_field_fixture] k = {}, proof = {} bytes, m = {} identities ({} gate)",
        fx.vk.k(),
        fx.proof.len(),
        manifest.entries.len(),
        manifest.gate_identities
    );

    if !pinned_solc_available() {
        eprintln!("skipping foreign-field EVM checks: pinned solc not available");
        return;
    }
    let instances = vec![fx.instance];
    let calldata = generator.encode_calldata(&fx.proof, &instances).expect("calldata encoding");
    let mut wrong = instances.clone();
    wrong[0] += F::ONE;
    let wrong_calldata = generator.encode_calldata(&fx.proof, &wrong).expect("calldata encoding");
    for lowering in [QuotientLowering::Vm, QuotientLowering::Direct] {
        let artifacts = generator
            .render(RenderOptions {
                vk: RenderVk::Separate,
                quotient_lowering: lowering,
                ..RenderOptions::default()
            })
            .expect("foreign-field render");
        let mut evm = Evm::default();
        let vk_address = evm.create(compile_solidity(
            artifacts.verifying_key.expect("separate VK"),
        ));
        let verifier =
            evm.create_with_address_arg(compile_solidity(&artifacts.verifier), vk_address);
        match evm.try_call_with_gas(verifier, calldata.clone(), 5_000_000_000) {
            CallOutcome::Success {
                gas_used, output, ..
            } => {
                assert_eq!(
                    output,
                    [vec![0u8; 31], vec![1]].concat(),
                    "{lowering:?} accepts"
                );
                eprintln!(
                    "foreign-field proof verified on-chain ({lowering:?}) in {gas_used} gas; verifier runtime {} bytes",
                    evm.code_size(verifier)
                );
            }
            other => panic!("{lowering:?} verifier rejected the foreign-field proof: {other:?}"),
        }
        if let CallOutcome::Success { output, .. } =
            evm.try_call_with_gas(verifier, wrong_calldata.clone(), 5_000_000_000)
        {
            assert_ne!(
                output,
                [vec![0u8; 31], vec![1]].concat(),
                "{lowering:?} verifier accepted a wrong public input"
            );
        }
    }

    #[cfg(feature = "rust-verifier-trace")]
    common::direct_trace::assert_direct_trace_matches_native(
        "foreign field",
        &generator,
        || {
            midnight_zk_stdlib::verify::<ForeignFieldCircuit, Keccak256>(
                &fx.srs.verifier_params(),
                &fx.vk,
                &fx.instance,
                None,
                &fx.proof,
            )
            .expect("native verifier (trace)")
        },
        &calldata,
    );
}

/// The emitted quotient Yul of both lowerings against the Rust reference on
/// the honest proof, random evaluation frames and changed challenges. Kept
/// separate from the acceptance test so that it reports a quotient bug by
/// bucket and identity even when the honest proof is rejected.
#[cfg(feature = "rust-verifier-trace")]
#[test]
fn foreign_field_quotient_probe_matches_the_rust_reference() {
    let Some(fx) = fixture() else { return };
    if !pinned_solc_available() {
        eprintln!("skipping foreign-field quotient probe: pinned solc not available");
        return;
    }
    let generator = generator(fx);
    common::quotient_probe::assert_quotient_probe_matches_rust::<Keccak256>(
        "foreign field",
        &generator,
        fx.vk.vk(),
        &fx.proof,
        &[fx.instance],
        1,
        0x7072_6f62_0005,
    );
}

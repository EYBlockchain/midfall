//! Helpers to produce an IVC-aggregated proof + verifying key matching
//! `aggregation/examples/single_circuit_aggregation.rs`.
//!
//! The IVC chain aggregates `STEPS` SHA-256 preimage proofs, with the
//! first `STEPS - 1` chain steps using the default Poseidon outer
//! transcript (matches the in-circuit verifier baked into `IvcCircuit`)
//! and the **final** step emitting its outer Fiat-Shamir transcript
//! under [`sha3::Keccak256`] via `IvcProver::prove_step_with`.  That
//! final-step proof is exactly the artefact this module exposes for
//! consumption by the on-chain Solidity `PlonkVerifier`.
//!
//! This file is a faithful port of `aggregation/examples/single_circuit_aggregation.rs`
//! plus its `common/sha_preimage.rs` helper, packaged as a `*Fixture`
//! struct so that `bin/generate_ivc.rs` and the in-process revm test
//! harness in `tests/ivc.rs` consume them uniformly.
//!
//! Notes on feature flags
//! ----------------------
//!
//!   * `aggregation/Cargo.toml` declares
//!     `required-features = ["truncated-challenges"]` for the example.
//!     The IVC machinery in `aggregation/src/ivc/*` itself compiles
//!     unconditionally; the example flag is mostly a knob to keep the
//!     in-circuit verifier accumulator math fitting into `k=19`.  This
//!     module compiles WITHOUT `truncated-challenges` so the wire
//!     format produced here is fully compatible with the existing
//!     poseidon/RSA Solidity verifier.  The trade-off is a slightly
//!     larger circuit; if the `IvcCircuit::cs_degree`-driven k turns
//!     out to overflow `2^19` rows, callers should set `IVC_K=20` in
//!     the environment and download the corresponding Midnight SRS.

use std::collections::BTreeMap;

use ff::Field;
use group::Group;
use midnight_aggregation::ivc::{
    self, IvcCircuit, IvcContext, IvcIO, IvcProver, IvcState, IvcTransition, IvcVerifier,
};
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{
        hash::HashCPU, AssignmentInstructions, PublicInputInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator, BlstrsEmulation, SelfEmulation},
};
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::{
        kzg::{params::ParamsKZG, KZGCommitmentScheme},
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{
    cs_degree,
    utils::plonk_api::{load_srs, SrsSource},
    MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};
use rand::{rngs::OsRng, Rng};
use sha2::Digest;
use sha3::Keccak256;

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type E = <S as SelfEmulation>::Engine;

// ===========================================================================
//                       Inner circuit (SHA-256 preimage)
// ===========================================================================

/// Replica of `aggregation/examples/common/sha_preimage.rs::ShaPreimageCircuit`.
///
/// Given a public SHA-256 digest `x`, proves knowledge of a 192-bit
/// preimage `w` such that `SHA-256(w) = x`.
#[derive(Clone, Debug, Default)]
pub struct ShaPreimageCircuit;

/// Circuit size parameter (log2 of rows) for the SHA preimage circuit.
///
/// Matches the value baked into `aggregation/examples/common/sha_preimage.rs`.
pub const INNER_K: u32 = 13;

/// Number of public input field elements (32 bytes, 1 field element each).
pub const INNER_NB_PUBLIC_INPUTS: usize = 32;

impl Relation for ShaPreimageCircuit {
    type Instance = [u8; 32];
    type Witness = [u8; 24]; // 192 = 24 * 8

    fn format_instance(instance: &Self::Instance) -> Result<Vec<F>, Error> {
        Ok(instance.iter().flat_map(AssignedByte::<F>::as_public_input).collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        _instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), Error> {
        let witness_bytes = witness.transpose_array();
        let assigned_input = std_lib.assign_many(layouter, &witness_bytes)?;
        let output = std_lib.sha2_256(layouter, &assigned_input)?;
        output.iter().try_for_each(|b| std_lib.constrain_as_public_input(layouter, b))
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            sha2_256: true,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(ShaPreimageCircuit)
    }
}

fn inner_constraint_system(
    arch: ZkStdLibArch,
    k: u32,
) -> (ConstraintSystem<F>, EvaluationDomain<F>) {
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (arch, (k - 1) as u8));
    let domain = EvaluationDomain::new(cs.degree() as u32, k);
    (cs, domain)
}

/// Generates a random instance-witness pair for the SHA preimage circuit.
fn random_inner_instance() -> ([u8; 32], [u8; 24]) {
    let preimage: [u8; 24] = OsRng.gen();
    let digest: [u8; 32] = sha2::Sha256::digest(preimage).into();
    (digest, preimage)
}

/// Proves a SHA-256 preimage statement using the Poseidon transcript
/// (matches the example).
fn prove_inner(
    srs: &ParamsKZG<E>,
    pk: &MidnightPK<ShaPreimageCircuit>,
    instance: &[u8; 32],
    witness: [u8; 24],
) -> Vec<u8> {
    midnight_zk_stdlib::prove::<ShaPreimageCircuit, PoseidonState<F>>(
        srs,
        pk,
        &ShaPreimageCircuit,
        instance,
        witness,
        OsRng,
    )
    .expect("inner SHA-256 preimage proof generation should not fail")
}

// ===========================================================================
//                         IVC transition (ProofAggregation)
// ===========================================================================

/// Setup data for the inner circuit, threaded as IVC context.
#[derive(Clone, Debug)]
pub struct InnerCircuitContext {
    pub cs: ConstraintSystem<F>,
    pub domain: EvaluationDomain<F>,
    pub vk: MidnightVK,
    pub params_verifier: midnight_proofs::poly::kzg::params::ParamsVerifierKZG<E>,
}

impl InnerCircuitContext {
    fn fixed_bases(&self) -> BTreeMap<String, C> {
        verifier::fixed_bases::<S>("inner_vk", self.vk.vk())
    }
}

/// Off-circuit IVC state for proof aggregation.
#[derive(Clone, Debug)]
pub struct State {
    pub statements: Vec<<ShaPreimageCircuit as Relation>::Instance>,
    pub statements_hash: F,
    pub inner_acc: Accumulator<S>,
}

/// In-circuit counterpart of [`State`] (constant size).
#[derive(Clone, Debug)]
pub struct AssignedState {
    pub statements_hash: AssignedNative<F>,
    pub inner_acc: AssignedAccumulator<S>,
}

/// Witness for a single aggregation step: an inner statement and its proof.
#[derive(Clone, Debug)]
pub struct AggregationWitness {
    pub inner_statement: <ShaPreimageCircuit as Relation>::Instance,
    pub inner_proof: Vec<u8>,
}

/// IVC transition that aggregates one inner proof per step.
#[derive(Clone, Debug)]
pub struct ProofAggregation {
    std_lib: ZkStdLib,
    inner_ctx: InnerCircuitContext,
}

impl IvcContext for ProofAggregation {
    type Context = InnerCircuitContext;

    fn new(std_lib: ZkStdLib, ctx: &InnerCircuitContext) -> Self {
        ProofAggregation {
            std_lib,
            inner_ctx: ctx.clone(),
        }
    }

    fn write_context<W: std::io::Write>(
        _ctx: &InnerCircuitContext,
        _writer: &mut W,
    ) -> std::io::Result<()> {
        unimplemented!("InnerCircuitContext serialization not implemented")
    }

    fn read_context<R: std::io::Read>(_reader: &mut R) -> std::io::Result<InnerCircuitContext> {
        unimplemented!("InnerCircuitContext deserialization not implemented")
    }
}

impl IvcState for ProofAggregation {
    type State = State;
    type AssignedState = AssignedState;

    fn genesis(ctx: &InnerCircuitContext) -> Self::State {
        State {
            statements: vec![],
            statements_hash: F::ZERO,
            inner_acc: Accumulator::<S>::trivial(
                &ctx.fixed_bases().keys().cloned().collect::<Vec<_>>(),
            ),
        }
    }

    fn is_genesis(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
    ) -> Result<AssignedBit<F>, Error> {
        self.std_lib.is_zero(layouter, &state.statements_hash)
    }

    fn decider(ctx: &InnerCircuitContext, state: &State) -> bool {
        let expected_hash = state.statements.iter().fold(F::ZERO, |h_acc, x| {
            let pis = ShaPreimageCircuit::format_instance(x).expect("valid instance");
            let h = <PoseidonChip<F> as HashCPU<F, F>>::hash(&pis);
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h, h_acc])
        });

        if expected_hash != state.statements_hash {
            return false;
        }

        state.inner_acc.check(&ctx.params_verifier, &ctx.fixed_bases())
    }
}

impl IvcIO for ProofAggregation {
    fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        value: Value<State>,
    ) -> Result<AssignedState, Error> {
        let statements_hash =
            self.std_lib.assign(layouter, value.as_ref().map(|s| s.statements_hash))?;

        let inner_acc = self.std_lib.verifier().assign_collapsed_accumulator(
            layouter,
            &self.inner_ctx.fixed_bases().keys().cloned().collect::<Vec<_>>(),
            value.as_ref().map(|s| s.inner_acc.clone()),
        )?;

        Ok(AssignedState {
            statements_hash,
            inner_acc,
        })
    }

    fn constrain_as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<(), Error> {
        self.std_lib.constrain_as_public_input(layouter, &state.statements_hash)?;
        self.std_lib.verifier().constrain_as_public_input(layouter, &state.inner_acc)
    }

    fn as_public_input(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &AssignedState,
    ) -> Result<Vec<AssignedNative<F>>, Error> {
        Ok([
            self.std_lib.as_public_input(layouter, &state.statements_hash)?,
            self.std_lib.verifier().as_public_input(layouter, &state.inner_acc)?,
        ]
        .concat())
    }

    fn format_public_input(state: &State) -> Vec<F> {
        [
            vec![state.statements_hash],
            AssignedAccumulator::<S>::as_public_input(&state.inner_acc),
        ]
        .concat()
    }
}

impl IvcTransition for ProofAggregation {
    type Witness = AggregationWitness;

    fn arch() -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn transition(
        ctx: &InnerCircuitContext,
        state: &Self::State,
        witness: Self::Witness,
    ) -> Self::State {
        let statement_pis =
            ShaPreimageCircuit::format_instance(&witness.inner_statement).expect("valid instance");

        let inner_proof_acc = {
            let mut transcript =
                CircuitTranscript::<PoseidonState<F>>::init_from_bytes(&witness.inner_proof);
            let dual_msm =
                plonk::prepare::<F, KZGCommitmentScheme<E>, CircuitTranscript<PoseidonState<F>>>(
                    ctx.vk.vk(),
                    &[&[C::identity()]],
                    &[&[&statement_pis]],
                    &mut transcript,
                )
                .expect("off-circuit prepare should succeed");

            assert!(
                dual_msm.clone().check(&ctx.params_verifier),
                "invalid inner proof"
            );

            Accumulator::from_dual_msm(dual_msm, "inner_vk", &ctx.fixed_bases())
        };

        let inner_acc = {
            let mut acc = Accumulator::accumulate(&[inner_proof_acc, state.inner_acc.clone()]);
            acc.collapse();
            acc
        };

        let statements_hash = {
            let h_statement = <PoseidonChip<F> as HashCPU<F, F>>::hash(&statement_pis);
            <PoseidonChip<F> as HashCPU<F, F>>::hash(&[h_statement, state.statements_hash])
        };

        let mut statements = state.statements.clone();
        statements.push(witness.inner_statement);

        State {
            statements,
            statements_hash,
            inner_acc,
        }
    }

    fn circuit_transition(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::AssignedState,
        witness: Value<Self::Witness>,
    ) -> Result<Self::AssignedState, Error> {
        let inner_vk = self.std_lib.verifier().assign_fixed_vk(
            layouter,
            "inner_vk",
            &self.inner_ctx.domain,
            &self.inner_ctx.cs,
            self.inner_ctx.vk.vk().transcript_repr(),
        )?;

        let statement_pis = self.std_lib.assign_many(
            layouter,
            &witness
                .as_ref()
                .map(|w| ShaPreimageCircuit::format_instance(&w.inner_statement).unwrap())
                .transpose_vec(INNER_NB_PUBLIC_INPUTS),
        )?;

        let id_point = self.std_lib.bls12_381_curve().assign_fixed(layouter, C::identity())?;

        let inner_proof_acc = self.std_lib.verifier().prepare(
            layouter,
            &inner_vk,
            &[id_point],
            &[&statement_pis],
            witness.map(|w| w.inner_proof),
        )?;

        let inner_acc = {
            let mut acc = self
                .std_lib
                .verifier()
                .accumulate(layouter, &[inner_proof_acc, state.inner_acc.clone()])?;

            acc.collapse(
                layouter,
                self.std_lib.bls12_381_curve(),
                self.std_lib.bls12_381_scalar(),
            )?;
            acc
        };

        let statements_hash = {
            let h_statement = self.std_lib.poseidon(layouter, &statement_pis)?;
            self.std_lib.poseidon(layouter, &[h_statement, state.statements_hash.clone()])?
        };

        Ok(AssignedState {
            statements_hash,
            inner_acc,
        })
    }
}

// ===========================================================================
//                           Fixture builder
// ===========================================================================

/// Default IVC circuit size parameter (log2 of rows).  Matches the
/// example.
pub const IVC_K: u32 = 19;

/// Default number of inner proofs aggregated by the chain.
pub const STEPS: usize = 3;

/// Bundle of artefacts produced by [`IvcAggregationFixture::build`]:
/// the SRS, verifying key, the final IVC instance's flat public-input
/// vector, and the **final-step** Keccak256-transcript proof bytes.
///
/// `vk_for_codegen` is the IVC circuit's `MidnightVK`; it is what
/// `VkInfo::from_live` consumes to render `IvcVerifyingKey.sol`.
pub struct IvcAggregationFixture {
    pub srs: ParamsKZG<E>,
    pub vk: MidnightVK,
    /// Public-input vector for the final IVC instance, in the order
    /// `IvcCircuit::format_instance` produces:
    ///
    ///   `[ vk_repr, statements_hash, inner_acc_pi..., ivc_acc_pi... ]`
    ///
    /// Ready to be passed verbatim as `bytes32[] publicInputs` to the
    /// on-chain Solidity `PlonkVerifier`.
    pub public_inputs: Vec<Fq>,
    /// Final-step proof bytes, emitted under the
    /// `CircuitTranscript<sha3::Keccak256>` outer transcript.
    pub proof: Vec<u8>,
}

impl IvcAggregationFixture {
    /// Drives the full chain with `STEPS` inner SHA-256 proofs, the
    /// first `STEPS - 1` outer steps using the Poseidon transcript and
    /// the **final** outer step using `sha3::Keccak256` (via
    /// `IvcProver::prove_step_with::<Keccak256>`).
    ///
    /// Returns the IVC verifying key + the final-step Keccak proof +
    /// the corresponding public-input vector.
    ///
    /// `ivc_k` defaults to [`IVC_K`] (k=19) when zero is passed.  Set
    /// it via the `IVC_K` env var if a future change to
    /// `ZkStdLib::configure` makes the IVC circuit overflow `2^19`
    /// rows; at that point you also need a Midnight SRS for the new
    /// `k` (`midnight-srs-2p<k>`) under `$SRS_DIR`.
    pub fn build(ivc_k: u32) -> Self {
        let ivc_k = if ivc_k == 0 { IVC_K } else { ivc_k };

        // Inner SRS / VK / PK.
        let inner_arch = ShaPreimageCircuit.used_chips();
        let inner_srs = load_srs(SrsSource::Filecoin, INNER_K, cs_degree(inner_arch));
        let inner_vk = midnight_zk_stdlib::setup_vk(&inner_srs, &ShaPreimageCircuit);
        let inner_pk = midnight_zk_stdlib::setup_pk(&ShaPreimageCircuit, &inner_vk);
        let inner_ctx = {
            let (inner_cs, inner_domain) = inner_constraint_system(inner_arch, INNER_K);
            InnerCircuitContext {
                cs: inner_cs,
                domain: inner_domain,
                vk: inner_vk,
                params_verifier: inner_srs.verifier_params(),
            }
        };

        // Inner proofs.
        eprintln!("[ivc] generating {STEPS} inner SHA-256 preimage proofs...");
        let inner_statements_with_witnesses: Vec<_> =
            (0..STEPS).map(|_| random_inner_instance()).collect();
        let inner_proofs: Vec<_> = inner_statements_with_witnesses
            .iter()
            .map(|(digest, preimage)| prove_inner(&inner_srs, &inner_pk, digest, *preimage))
            .collect();
        let inner_statements: Vec<_> =
            inner_statements_with_witnesses.into_iter().map(|(x, _)| x).collect();

        // IVC setup.
        eprintln!("[ivc] IVC setup at k={ivc_k}...");
        let ivc_srs = load_srs(
            SrsSource::Midnight,
            ivc_k,
            IvcCircuit::<ProofAggregation>::cs_degree(),
        );
        let (mut prover, ivc_verifier): (IvcProver<ProofAggregation>, IvcVerifier) =
            ivc::setup::<ProofAggregation>(ivc_srs.clone(), ivc_k, inner_ctx.clone());

        // Chain steps.
        let mut keccak_proof: Option<Vec<u8>> = None;
        for i in 0..STEPS {
            let ivc_witness = AggregationWitness {
                inner_statement: inner_statements[i],
                inner_proof: inner_proofs[i].clone(),
            };
            let is_final = i + 1 == STEPS;

            let ivc_proof = if is_final {
                prover.prove_step_with::<Keccak256>(ivc_witness).expect("final keccak step")
            } else {
                prover.prove_step(ivc_witness).expect("intermediate poseidon step")
            };

            // Sanity-check each step before moving on.
            let ivc_instance = prover.instance();
            if is_final {
                ivc_verifier
                    .verify_with::<ProofAggregation, Keccak256>(
                        &inner_ctx,
                        &ivc_instance,
                        &ivc_proof,
                    )
                    .expect("native verifier accepts final keccak proof");
            } else {
                ivc_verifier
                    .verify(&inner_ctx, &ivc_instance, &ivc_proof)
                    .expect("native verifier accepts intermediate poseidon proof");
            }

            if is_final {
                keccak_proof = Some(ivc_proof);
            }
        }
        let proof = keccak_proof.expect("STEPS >= 1");

        // Recover the canonical IVC verifying key + the final
        // instance's public-input vector.
        let vk = midnight_zk_stdlib::setup_vk(
            &ivc_srs,
            &IvcCircuit::<ProofAggregation>::new(
                EvaluationDomain::new(IvcCircuit::<ProofAggregation>::cs_degree() as u32, ivc_k),
                {
                    let mut cs = ConstraintSystem::default();
                    ZkStdLib::configure(
                        &mut cs,
                        (IvcCircuit::<ProofAggregation>::arch(), (ivc_k - 1) as u8),
                    );
                    cs
                },
                inner_ctx.clone(),
            ),
        );
        let final_instance = prover.instance();
        let public_inputs = IvcCircuit::<ProofAggregation>::format_instance(&final_instance)
            .expect("format_instance should not fail");

        Self {
            srs: ivc_srs,
            vk,
            public_inputs,
            proof,
        }
    }
}

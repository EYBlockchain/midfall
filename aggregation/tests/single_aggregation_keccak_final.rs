//! End-to-end test: aggregate three SHA-256 preimage proofs over an IVC
//! chain (the same shape as `examples/single_circuit_aggregation.rs`),
//! emit the **final** chain proof under a Keccak-256 transcript via
//! `IvcProver::prove_final_step`, and verify that final proof
//! off-circuit via `IvcVerifier::verify_final`.
//!
//! Required features: `keccak-transcript`, `truncated-challenges`,
//! `fewer-point-sets`. Run with:
//!
//! ```text
//! cargo test --release \
//!   --manifest-path /Users/Julien.Coolen/midfall/aggregation/Cargo.toml \
//!   --test single_aggregation_keccak_final \
//!   --features keccak-transcript,truncated-challenges,fewer-point-sets \
//!   -- --ignored --nocapture
//! ```
//!
//! This is the off-circuit twin of an EVM Solidity verifier on the
//! same IVC final proof: same Fiat-Shamir transcript (Keccak-256),
//! same multi-open scheme heuristic (`fewer-point-sets`), same
//! challenge truncation (`truncated-challenges`).
//!
//! Marked `#[ignore]` because IVC at `k = 19` over 3 SHA-256 chain
//! steps takes ~10-20 minutes on a typical laptop.

#![cfg(all(
    feature = "keccak-transcript",
    feature = "truncated-challenges",
    feature = "fewer-point-sets",
))]

#[path = "../examples/common/mod.rs"]
mod common;

use std::{collections::BTreeMap, time::Instant};

use common::sha_preimage::ShaPreimageCircuit;
use ff::Field;
use group::Group;
use midnight_aggregation::ivc::{self, IvcCircuit, IvcContext, IvcIO, IvcState, IvcTransition};
use midnight_circuits::{
    hash::poseidon::{PoseidonChip, PoseidonState},
    instructions::{hash::HashCPU, *},
    types::{AssignedBit, AssignedNative, Instantiable},
    verifier::{self, Accumulator, AssignedAccumulator, BlstrsEmulation, SelfEmulation},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, ConstraintSystem, Error},
    poly::{
        kzg::{params::ParamsVerifierKZG, KZGCommitmentScheme},
        EvaluationDomain,
    },
    transcript::{CircuitTranscript, Transcript},
};
use midnight_zk_stdlib::{
    cs_degree,
    utils::plonk_api::{load_srs, SrsSource},
    MidnightVK, Relation, ZkStdLib, ZkStdLibArch,
};

use crate::common::sha_preimage;

type S = BlstrsEmulation;
type F = <S as SelfEmulation>::F;
type C = <S as SelfEmulation>::C;
type E = <S as SelfEmulation>::Engine;

type InnerCircuit = ShaPreimageCircuit;

/// Setup data for the inner circuit, threaded as IVC context.
#[derive(Clone, Debug)]
pub struct InnerCircuitContext {
    cs: ConstraintSystem<F>,
    domain: EvaluationDomain<F>,
    vk: MidnightVK,
    params_verifier: ParamsVerifierKZG<E>,
}

impl InnerCircuitContext {
    fn fixed_bases(&self) -> BTreeMap<String, C> {
        verifier::fixed_bases::<S>("inner_vk", self.vk.vk())
    }
}

#[derive(Clone, Debug)]
pub struct State {
    statements: Vec<<InnerCircuit as Relation>::Instance>,
    statements_hash: F,
    inner_acc: Accumulator<S>,
}

#[derive(Clone, Debug)]
pub struct AssignedState {
    statements_hash: AssignedNative<F>,
    inner_acc: AssignedAccumulator<S>,
}

#[derive(Clone, Debug)]
pub struct AggregationWitness {
    pub inner_statement: <InnerCircuit as Relation>::Instance,
    pub inner_proof: Vec<u8>,
}

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
                .transpose_vec(sha_preimage::NB_PUBLIC_INPUTS),
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

#[test]
#[ignore = "slow IVC proving (~10-20 minutes); run with --ignored --nocapture"]
fn single_aggregation_final_proof_under_keccak() {
    const IVC_K: u32 = 19;
    const STEPS: usize = 1;

    // ----------------------------------------------------------
    // Inner circuit setup (Filecoin SRS, SHA-256 preimage at k = 13).
    // ----------------------------------------------------------
    let inner_arch = ShaPreimageCircuit.used_chips();
    let inner_srs = load_srs(SrsSource::Filecoin, sha_preimage::K, cs_degree(inner_arch));
    let inner_vk = sha_preimage::setup_vk(&inner_srs);
    let inner_pk = sha_preimage::setup_pk(&inner_vk);
    let inner_ctx = {
        let (inner_cs, inner_domain) = common::constraint_system(inner_arch, sha_preimage::K);
        InnerCircuitContext {
            cs: inner_cs,
            domain: inner_domain,
            vk: inner_vk,
            params_verifier: inner_srs.verifier_params(),
        }
    };

    // ----------------------------------------------------------
    // Generate the STEPS inner statements + Poseidon-transcript proofs.
    // ----------------------------------------------------------
    let start = Instant::now();
    let inner_statements_with_witnesses: [_; STEPS] =
        std::array::from_fn(|_| sha_preimage::random_instance());
    let inner_proofs: [_; STEPS] = std::array::from_fn(|i| {
        let (digest, preimage) = &inner_statements_with_witnesses[i];
        sha_preimage::prove(&inner_srs, &inner_pk, digest, *preimage)
    });
    let inner_statements = inner_statements_with_witnesses.map(|(x, _)| x);
    println!(
        "[keccak-final] {STEPS} inner SHA-256 proofs generated in {:.2?}",
        start.elapsed()
    );

    // ----------------------------------------------------------
    // IVC setup. Midnight SRS at k = 19 (matches the example).
    // ----------------------------------------------------------
    let ivc_srs = load_srs(
        SrsSource::Midnight,
        IVC_K,
        IvcCircuit::<ProofAggregation>::cs_degree(),
    );
    let start = Instant::now();
    let (mut prover, verifier) = ivc::setup::<ProofAggregation>(ivc_srs, IVC_K, inner_ctx.clone());
    println!("[keccak-final] IVC setup completed in {:.2?}", start.elapsed());

    // ----------------------------------------------------------
    // Aggregation chain: STEPS-1 Poseidon-transcript steps, then a
    // final Keccak-transcript step.
    // ----------------------------------------------------------
    for i in 0..STEPS - 1 {
        let ivc_witness = AggregationWitness {
            inner_statement: inner_statements[i],
            inner_proof: inner_proofs[i].clone(),
        };

        let start = Instant::now();
        let ivc_proof = prover.prove_step(ivc_witness).unwrap();
        let prove_time = start.elapsed();

        let ivc_instance = prover.instance();
        let start = Instant::now();
        verifier.verify(&inner_ctx, &ivc_instance, &ivc_proof).unwrap();
        let verify_time = start.elapsed();

        println!(
            "[keccak-final] Step {i} (Poseidon): prove {prove_time:.2?}, verify {verify_time:.2?}"
        );
    }

    // Final step: emit the proof under a Keccak-256 transcript.
    let last = STEPS - 1;
    let final_witness = AggregationWitness {
        inner_statement: inner_statements[last],
        inner_proof: inner_proofs[last].clone(),
    };

    let start = Instant::now();
    let final_proof = prover
        .prove_final_step(final_witness)
        .expect("prove_final_step should succeed on the last chain step");
    let prove_time = start.elapsed();
    let final_instance = prover.instance();
    println!(
        "[keccak-final] Step {last} (Keccak):   prove {prove_time:.2?} ({} bytes)",
        final_proof.len()
    );

    // Off-circuit verify_final under Keccak-256.
    let start = Instant::now();
    verifier
        .verify_final::<ProofAggregation>(&inner_ctx, &final_instance, &final_proof)
        .expect("verify_final must accept the prove_final_step output");
    let verify_time = start.elapsed();
    println!("[keccak-final] verify_final completed in {:.2?}", verify_time);

    // Cross-transcript guard: regular `verify` (Poseidon) must reject the
    // Keccak-transcript proof. Catches accidental fall-back.
    let crossed = verifier.verify::<ProofAggregation>(&inner_ctx, &final_instance, &final_proof);
    assert!(
        crossed.is_err(),
        "Poseidon-transcript verify must NOT accept a Keccak-transcript proof"
    );
    println!("[keccak-final] cross-transcript rejection: OK");

    // Sanity: the final state must contain all STEPS aggregated statements.
    let final_state = final_instance.state().clone();
    assert_eq!(final_state.statements.len(), STEPS);
    println!(
        "[keccak-final] aggregated {STEPS} SHA-256 statements; statements_hash = {:?}",
        final_state.statements_hash
    );

    println!("[keccak-final] PASS");
}

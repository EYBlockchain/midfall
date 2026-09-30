//! Shared helpers for the EVM fixture tests.
//!
//! `direct_trace` runs the native Midfall verifier with the Rust trace hooks
//! (`midnight_proofs::plonk::solidity_trace`, enabled by the
//! `rust-verifier-trace` feature) and a direct-lowering trace render of the
//! same proof, then compares every shared trace id byte for byte and every
//! direct-lowering intermediate (helper-call results, product-table entries,
//! limb-view words; ids `DIRECT_TRACE_HELPER_BASE..DIRECT_TRACE_END`) against
//! the generator's native expected values.

#![allow(dead_code)]

#[cfg(feature = "rust-verifier-trace")]
pub mod direct_trace {
    use std::collections::BTreeMap;

    use halo2_solidity_verifier::{
        compile_solidity, revm, Evm, QuotientLowering, RenderDiagnostics, RenderOptions, RenderVk,
        SolidityGenerator, DIRECT_TRACE_END, DIRECT_TRACE_HELPER_BASE,
    };
    use midnight_curves::Fq;
    use midnight_proofs::plonk::solidity_trace;

    /// Counts of one trace comparison.
    #[derive(Debug)]
    pub struct TraceComparison {
        pub shared_ids: usize,
        pub intermediates: usize,
        pub gas_used: u64,
    }

    fn parse_logs(logs: &[revm::primitives::Log]) -> BTreeMap<u64, Vec<u8>> {
        let mut trace = BTreeMap::new();
        for log in logs {
            let topics = log.data.topics();
            let data = log.data.data.as_ref().to_vec();
            if topics.len() != 1 || data.is_empty() {
                continue;
            }
            let id = u64::from_be_bytes(topics[0].as_slice()[24..32].try_into().unwrap());
            assert!(
                trace.insert(id, data).is_none(),
                "duplicate Solidity trace id {id}"
            );
        }
        trace
    }

    /// Run `native` under the Rust trace hooks, render the direct-lowering
    /// trace verifier, call it with `calldata`, and compare.
    pub fn assert_direct_trace_matches_native(
        label: &str,
        generator: &SolidityGenerator<'_>,
        native: impl FnOnce(),
        calldata: &[u8],
    ) -> TraceComparison {
        solidity_trace::start();
        native();
        let rust = solidity_trace::take();
        assert_direct_trace_matches_native_events(label, generator, rust, calldata)
    }

    /// Same as [`assert_direct_trace_matches_native`] with an already
    /// collected native trace.
    pub fn assert_direct_trace_matches_native_events(
        label: &str,
        generator: &SolidityGenerator<'_>,
        rust: Vec<solidity_trace::SolidityTraceEvent>,
        calldata: &[u8],
    ) -> TraceComparison {
        let mut rust_by_id = BTreeMap::new();
        for event in rust {
            assert!(
                rust_by_id.insert(event.id, (event.name, event.data)).is_none(),
                "{label}: duplicate Rust trace id {}",
                event.id
            );
        }
        assert!(!rust_by_id.is_empty(), "{label}: native trace is empty");

        let artifacts = generator
            .render(RenderOptions {
                vk: RenderVk::Separate,
                quotient_lowering: QuotientLowering::Direct,
                diagnostics: RenderDiagnostics {
                    trace: true,
                    ..RenderDiagnostics::default()
                },
                ..RenderOptions::default()
            })
            .expect("direct trace render");
        let mut evm = Evm::default();
        let vk = evm.create(compile_solidity(
            artifacts.verifying_key.expect("separate VK"),
        ));
        let verifier = evm.create_with_address_arg(compile_solidity(&artifacts.verifier), vk);
        let (gas_used, output, logs) = evm.call_with_logs(verifier, calldata.to_vec());
        assert_eq!(
            output,
            [vec![0u8; 31], vec![1]].concat(),
            "{label}: direct trace verifier should accept the proof"
        );

        let solidity = parse_logs(&logs);
        let range = DIRECT_TRACE_HELPER_BASE..DIRECT_TRACE_END;
        let mut shared = 0usize;
        for (id, (name, rust_data)) in &rust_by_id {
            let sol = solidity.get(id).unwrap_or_else(|| {
                panic!("{label}: Solidity trace is missing native id {id} ({name})")
            });
            assert_eq!(
                rust_data,
                sol,
                "{label}: trace mismatch id={id} name={name}: rust=0x{} solidity=0x{}",
                hex::encode(rust_data),
                hex::encode(sol)
            );
            shared += 1;
        }
        // 29 / 30 are the public-accumulator points, traced by the generator
        // only (outside the native PLONK verifier), as in the IVC trace test.
        for id in solidity.keys().filter(|id| !range.contains(id) && ![29, 30].contains(*id)) {
            assert!(
                rust_by_id.contains_key(id),
                "{label}: Solidity id {id} has no native oracle"
            );
        }
        assert!(
            rust_by_id.keys().any(|id| (30_000..40_000).contains(id)),
            "{label}: no quotient identity values compared"
        );

        let base = solidity_trace::PROOF_EVAL_TRACE_BASE;
        let evals: Vec<Fq> = (0u64..)
            .map_while(|i| rust_by_id.get(&(base + i)))
            .map(|(_, data)| {
                let word: [u8; 32] = data.as_slice().try_into().unwrap();
                Option::<Fq>::from(Fq::from_bytes_be(&word)).unwrap()
            })
            .collect();
        let expected = generator
            .direct_quotient_trace_values(&evals)
            .expect("native direct trace values");
        let mut mismatches = Vec::new();
        for (id, name, value) in &expected {
            let want = value.to_bytes_be().to_vec();
            match solidity.get(id) {
                Some(got) if *got == want => {}
                Some(got) => mismatches.push(format!(
                    "id={id} name={name}: native=0x{} solidity=0x{}",
                    hex::encode(&want),
                    hex::encode(got)
                )),
                None => mismatches.push(format!("id={id} name={name}: missing in Solidity trace")),
            }
        }
        let expected_ids: std::collections::BTreeSet<u64> =
            expected.iter().map(|(id, _, _)| *id).collect();
        for id in solidity.keys().filter(|id| range.contains(id) && !expected_ids.contains(id)) {
            mismatches.push(format!(
                "id={id}: emitted by Solidity without a native value"
            ));
        }
        assert!(
            mismatches.is_empty(),
            "{label}: {} direct intermediate mismatches:\n{}",
            mismatches.len(),
            mismatches.join("\n")
        );
        eprintln!(
            "[direct-trace] {label}: {shared} shared trace ids and {} direct intermediates compared, 0 mismatches",
            expected.len()
        );
        TraceComparison {
            shared_ids: shared,
            intermediates: expected.len(),
            gas_used,
        }
    }
}

/// EVM-level differential test of the emitted quotient Yul.
///
/// `SolidityGenerator::render_quotient_probe` renders a test-only copy of the
/// verifier that returns `[expected_eval, selector_acc[0..n)]` right after the
/// quotient section. The probe (Direct and Vm lowerings) is run on the honest
/// proof, on random evaluation frames (every main evaluation scalar of the
/// proof replaced by a random field element) and on a frame with a changed
/// public input (new transcript, so new theta / beta / gamma / trash / y / x),
/// and compared word by word with a Rust reference:
///
/// * identity values `e_j`: midnight-proofs' own `partially_evaluate_identities`
///   on the same (randomised) proof, read from the native verifier trace
///   (`30_000 + j`); this is the Rust reference for the permutation, lookup and
///   trash identities. Gate identities are additionally re-evaluated here with
///   `Expression::evaluate` on the same evaluations and must agree;
/// * the fold: `compute_linearization_commitment`'s rule, identity `j` weighted
///   `y^(m-1-j)`, grouped by the gate's simple selector column (ascending
///   column order) or negated into `expected_eval`; cross-checked against the
///   native `quotient_numerator` (36) and `selector_fold` (60_000 + i) trace.
///
/// On a mismatch the failing bucket is named with the identities folded into
/// it, and a trace render of the same lowering localises the first differing
/// identity values.
#[cfg(feature = "rust-verifier-trace")]
pub mod quotient_probe {
    use std::collections::BTreeMap;

    use ff::{Field, PrimeField};
    use group::Group;
    use halo2_solidity_verifier::{
        compile_solidity, revm::primitives::Address, CallOutcome, Evm, QuotientIdentitySource,
        QuotientLowering, RenderDiagnostics, RenderOptions, RenderVk, SolidityGenerator,
    };
    use midnight_curves::{Bls12, Fq, G1Projective};
    use midnight_proofs::{
        plonk::{prepare, solidity_trace, VerifyingKey},
        poly::kzg::KZGCommitmentScheme,
        transcript::{
            CircuitTranscript, Hashable, Sampleable, Transcript, TranscriptHash,
            TranscriptInputBytes,
        },
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    /// Random evaluation frames per circuit (plus the honest proof and one
    /// frame with changed challenges).
    pub const RANDOM_FRAMES: usize = 8;

    /// Native trace names of the main evaluation scalars (everything the
    /// quotient section reads; PCS dummy / q evaluations excluded).
    const MAIN_EVAL_NAMES: &[&str] = &[
        "proof_committed_instance_eval",
        "proof_advice_eval",
        "proof_fixed_eval",
        "proof_permutation_common_eval",
        "proof_permutation_product_eval",
        "proof_permutation_product_next_eval",
        "proof_permutation_product_last_eval",
        "proof_lookup_multiplicity_eval",
        "proof_lookup_helper_eval",
        "proof_lookup_accumulator_eval",
        "proof_lookup_accumulator_next_eval",
        "proof_trash_eval",
    ];
    const PROOF_EVAL_BASE: u64 = solidity_trace::PROOF_EVAL_TRACE_BASE;
    const IDENTITY_BASE: u64 = solidity_trace::QUOTIENT_IDENTITY_TRACE_BASE;
    const NUMERATOR_ID: u64 = solidity_trace::QUOTIENT_NUMERATOR_TRACE_ID;
    const SELECTOR_FOLD_BASE: u64 = solidity_trace::SELECTOR_FOLD_TRACE_BASE;
    const USER_CHALLENGE_BASE: u64 = solidity_trace::USER_CHALLENGE_TRACE_BASE;
    const Y_ID: u64 = 10;
    const INSTANCE_EVAL_ID: u64 = 22;

    type Vk = VerifyingKey<Fq, KZGCommitmentScheme<Bls12>>;
    type Events = BTreeMap<u64, (&'static str, Vec<u8>)>;

    /// Counts of one probe comparison.
    #[derive(Debug)]
    pub struct ProbeReport {
        /// Frames compared (honest + random + changed challenges).
        pub frames: usize,
        /// Frames with changed challenges.
        pub changed_challenge_frames: usize,
        /// Identities `m`.
        pub identities: usize,
        /// Gate identities re-evaluated with `Expression::evaluate`.
        pub gate_identities: usize,
        /// Selector buckets (output words `1..=n`).
        pub selector_buckets: usize,
        /// Lowerings compared (Direct, Vm).
        pub lowerings: usize,
    }

    fn fq(data: &[u8]) -> Fq {
        let word: [u8; 32] = data.try_into().expect("32-byte trace word");
        Option::<Fq>::from(Fq::from_bytes_be(&word)).expect("canonical trace word")
    }

    fn hex(value: &Fq) -> String {
        format!("0x{}", hex::encode(value.to_bytes_be()))
    }

    /// Run midnight-proofs' verifier (`prepare`, which evaluates every
    /// identity) on `proof` under the trace hooks. A randomised frame fails
    /// later (PCS); the identity events are recorded before that.
    fn native_events<H: TranscriptHash>(vk: &Vk, proof: &[u8], instances: &[Fq]) -> Events
    where
        G1Projective: Hashable<H>,
        Fq: Hashable<H> + Sampleable<H>,
        H::Input: TranscriptInputBytes,
    {
        solidity_trace::start();
        let mut transcript = CircuitTranscript::<H>::init_from_bytes(proof);
        let _ = prepare::<Fq, KZGCommitmentScheme<Bls12>, CircuitTranscript<H>>(
            vk,
            &[&[G1Projective::identity()]],
            &[&[instances]],
            &mut transcript,
        );
        let mut events = BTreeMap::new();
        for event in solidity_trace::take() {
            assert!(
                events.insert(event.id, (event.name, event.data)).is_none(),
                "duplicate native trace id {}",
                event.id
            );
        }
        events
    }

    /// Main evaluation scalars of a native trace, in proof read order.
    fn main_evals(events: &Events) -> Vec<Fq> {
        (0u64..)
            .map_while(|i| events.get(&(PROOF_EVAL_BASE + i)))
            .filter(|(name, _)| MAIN_EVAL_NAMES.contains(name))
            .map(|(_, data)| fq(data))
            .collect()
    }

    /// Byte offset of the (contiguous) main evaluation scalars in `proof`.
    fn eval_offset(proof: &[u8], evals: &[Fq]) -> usize {
        let reprs: Vec<Vec<u8>> = evals.iter().map(|v| v.to_repr().as_ref().to_vec()).collect();
        let len = 32 * evals.len();
        let offsets: Vec<usize> = (0..=proof.len().saturating_sub(len))
            .filter(|o| {
                (0..evals.len()).all(|i| proof[o + 32 * i..o + 32 * (i + 1)] == reprs[i][..])
            })
            .collect();
        assert_eq!(
            offsets.len(),
            1,
            "main evaluation scalars must occur exactly once, contiguously, in the proof"
        );
        offsets[0]
    }

    /// Rust reference of one frame.
    struct Reference {
        m: usize,
        e: Vec<Fq>,
        /// Selector bucket of identity `j` (`None`: expected_eval).
        bucket: Vec<Option<usize>>,
        expected_eval: Fq,
        selector_acc: Vec<Fq>,
        gate_identities: usize,
    }

    fn reference(
        label: &str,
        vk: &Vk,
        events: &Events,
        nb_committed_instances: usize,
        selector_columns: &[usize],
    ) -> Reference {
        let cs = vk.cs();
        let m = (0u64..).take_while(|j| events.contains_key(&(IDENTITY_BASE + j))).count();
        assert!(m > 0, "{label}: native trace has no identity values");
        let e: Vec<Fq> = (0..m).map(|j| fq(&events[&(IDENTITY_BASE + j as u64)].1)).collect();
        let y = fq(&events[&Y_ID].1);

        // Evaluations as midnight-proofs' verifier indexes them.
        let by_name = |name: &str| -> Vec<Fq> {
            (0u64..)
                .map_while(|i| events.get(&(PROOF_EVAL_BASE + i)))
                .filter(|(n, _)| *n == name)
                .map(|(_, data)| fq(data))
                .collect()
        };
        let advice = by_name("proof_advice_eval");
        assert_eq!(
            advice.len(),
            cs.advice_queries().len(),
            "{label}: advice evals"
        );
        let mut fixed_read = by_name("proof_fixed_eval").into_iter();
        let fixed: Vec<Fq> = cs
            .fixed_queries()
            .iter()
            .map(|(column, _)| {
                if cs.has_simple_selector_col(column.index()) {
                    Fq::ONE
                } else {
                    fixed_read.next().expect("fixed eval")
                }
            })
            .collect();
        let mut committed = by_name("proof_committed_instance_eval").into_iter();
        let first_public = cs
            .instance_queries()
            .iter()
            .position(|(column, _)| column.index() >= nb_committed_instances);
        let instance: Vec<Option<Fq>> = cs
            .instance_queries()
            .iter()
            .enumerate()
            .map(|(i, (column, _))| {
                if column.index() < nb_committed_instances {
                    committed.next()
                } else if Some(i) == first_public {
                    events.get(&INSTANCE_EVAL_ID).map(|(_, data)| fq(data))
                } else {
                    None
                }
            })
            .collect();
        let challenge = |i: usize| fq(&events[&(USER_CHALLENGE_BASE + i as u64)].1);

        // Gate identities: Expression::evaluate on the same evaluations.
        let mut bucket = vec![None; m];
        let mut j = 0usize;
        for gate in cs.gates() {
            let target = gate
                .queried_selectors()
                .iter()
                .filter(|s| s.is_simple())
                .map(|s| s.index())
                .next();
            for (p, poly) in gate.polynomials().iter().enumerate() {
                let value = poly.evaluate(
                    &|c| c,
                    &|_| panic!("virtual selector in a gate polynomial"),
                    &|q| {
                        let i = cs
                            .fixed_queries()
                            .iter()
                            .position(|(c, r)| c.index() == q.column_index() && *r == q.rotation())
                            .expect("fixed query");
                        fixed[i]
                    },
                    &|q| {
                        let i = cs
                            .advice_queries()
                            .iter()
                            .position(|(c, r)| c.index() == q.column_index() && *r == q.rotation())
                            .expect("advice query");
                        advice[i]
                    },
                    &|q| {
                        let i = cs
                            .instance_queries()
                            .iter()
                            .position(|(c, r)| c.index() == q.column_index() && *r == q.rotation())
                            .expect("instance query");
                        instance[i].expect(
                            "gate reads a computed instance evaluation other than the first",
                        )
                    },
                    &|c| challenge(c.index()),
                    &|a| -a,
                    &|a, b| a + b,
                    &|a, b| a * b,
                    &|a, c| a * c,
                );
                assert_eq!(
                    value,
                    e[j],
                    "{label}: Expression::evaluate of cs.gates()[..] \"{}\" polynomial[{p}] (identity {j}) disagrees with midnight-proofs' identity value",
                    gate.name()
                );
                bucket[j] = target.map(|col| {
                    selector_columns.iter().position(|c| *c == col).unwrap_or_else(|| {
                        panic!("{label}: simple selector column {col} has no bucket")
                    })
                });
                j += 1;
            }
        }
        let gate_identities = j;

        // compute_linearization_commitment: identity j carries y^(m-1-j).
        let mut expected_eval = Fq::ZERO;
        let mut selector_acc = vec![Fq::ZERO; selector_columns.len()];
        let mut y_pow = Fq::ONE;
        for j in (0..m).rev() {
            match bucket[j] {
                Some(s) => selector_acc[s] += y_pow * e[j],
                None => expected_eval -= y_pow * e[j],
            }
            y_pow *= y;
        }
        // Cross-check with midnight-proofs' own fold trace.
        assert_eq!(
            -expected_eval,
            fq(&events[&NUMERATOR_ID].1),
            "{label}: Rust fold disagrees with the native quotient_numerator trace"
        );
        let used: Vec<usize> =
            (0..selector_columns.len()).filter(|s| bucket.contains(&Some(*s))).collect();
        for (idx, s) in used.iter().enumerate() {
            assert_eq!(
                selector_acc[*s],
                fq(&events[&(SELECTOR_FOLD_BASE + idx as u64)].1),
                "{label}: Rust fold of selector column {} disagrees with the native selector_fold trace",
                selector_columns[*s]
            );
        }
        Reference {
            m,
            e,
            bucket,
            expected_eval,
            selector_acc,
            gate_identities,
        }
    }

    fn source_names(generator: &SolidityGenerator<'_>) -> Vec<String> {
        generator
            .quotient_identity_manifest()
            .entries
            .iter()
            .map(|entry| match &entry.source {
                QuotientIdentitySource::Gate {
                    gate_index,
                    gate_name,
                    polynomial_index,
                    ..
                } => format!(
                    "cs.gates()[{gate_index}] \"{gate_name}\" polynomial[{polynomial_index}]"
                ),
                QuotientIdentitySource::Permutation { identity_index } => {
                    format!("permutation identity {identity_index}")
                }
                QuotientIdentitySource::Lookup {
                    identity_index,
                    lookup_index,
                    ..
                } => format!("lookup {lookup_index} identity {identity_index}"),
                QuotientIdentitySource::Trash { trash_index, .. } => {
                    format!("trash {trash_index}")
                }
            })
            .collect()
    }

    /// Identity values emitted by a trace render of `lowering` on `calldata`
    /// that differ from the native values.
    fn localise(
        generator: &SolidityGenerator<'_>,
        lowering: QuotientLowering,
        calldata: &[u8],
        reference: &Reference,
        names: &[String],
    ) -> Vec<String> {
        let artifacts = generator
            .render(RenderOptions {
                vk: RenderVk::Separate,
                quotient_lowering: lowering,
                diagnostics: RenderDiagnostics {
                    trace: true,
                    ..RenderDiagnostics::default()
                },
                ..RenderOptions::default()
            })
            .expect("trace render");
        let mut evm = Evm::default();
        let vk = evm.create(compile_solidity(
            artifacts.verifying_key.expect("separate VK"),
        ));
        let verifier = evm.create_with_address_arg(compile_solidity(&artifacts.verifier), vk);
        let (_, _, logs) = evm.call_with_logs(verifier, calldata.to_vec());
        let mut sol = BTreeMap::new();
        for log in &logs {
            let topics = log.data.topics();
            if topics.len() == 1 {
                let id = u64::from_be_bytes(topics[0].as_slice()[24..32].try_into().unwrap());
                sol.insert(id, log.data.data.as_ref().to_vec());
            }
        }
        (0..reference.m)
            .filter_map(|j| {
                let got = sol.get(&(IDENTITY_BASE + j as u64)).map(|d| fq(d));
                (got != Some(reference.e[j])).then(|| {
                    format!(
                        "identity {j} ({}): emitted {} native {}",
                        names.get(j).map(String::as_str).unwrap_or("?"),
                        got.map(|v| hex(&v)).unwrap_or_else(|| "missing".into()),
                        hex(&reference.e[j])
                    )
                })
            })
            .collect()
    }

    /// Run the probe differential for one circuit (see the module docs).
    #[allow(clippy::too_many_arguments)]
    pub fn assert_quotient_probe_matches_rust<H: TranscriptHash>(
        label: &str,
        generator: &SolidityGenerator<'_>,
        vk: &Vk,
        proof: &[u8],
        instances: &[Fq],
        nb_committed_instances: usize,
        seed: u64,
    ) -> ProbeReport
    where
        G1Projective: Hashable<H>,
        Fq: Hashable<H> + Sampleable<H>,
        H::Input: TranscriptInputBytes,
    {
        let lowerings = [QuotientLowering::Direct, QuotientLowering::Vm];
        let mut evm = Evm::default();
        let mut probes: Vec<(QuotientLowering, Address)> = Vec::new();
        let mut selector_columns: Option<Vec<usize>> = None;
        for lowering in lowerings {
            let probe = generator
                .render_quotient_probe(lowering)
                .unwrap_or_else(|err| panic!("{label}: {lowering:?} probe render: {err}"));
            assert!(probe.verifier.contains("TEST-ONLY QUOTIENT PROBE"));
            match &selector_columns {
                None => selector_columns = Some(probe.selector_columns.clone()),
                Some(cols) => assert_eq!(cols, &probe.selector_columns),
            }
            let vk_address = evm.create(compile_solidity(&probe.verifying_key));
            let address =
                evm.create_with_address_arg(compile_solidity(&probe.verifier), vk_address);
            probes.push((lowering, address));
        }
        let selector_columns = selector_columns.expect("probe rendered");
        // Bucket order: ascending simple-selector fixed columns (the order of
        // compute_linearization_commitment's BTreeMap).
        let cs_simple: Vec<usize> = (0..vk.cs().num_fixed_columns())
            .filter(|c| vk.cs().has_simple_selector_col(*c))
            .collect();
        assert_eq!(
            selector_columns, cs_simple,
            "{label}: selector bucket order"
        );
        let names = source_names(generator);

        let honest = native_events::<H>(vk, proof, instances);
        let honest_evals = main_evals(&honest);
        let offset = eval_offset(proof, &honest_evals);
        let honest_y = fq(&honest[&Y_ID].1);

        let mut frames = Vec::new();
        frames.push((
            "honest proof".to_string(),
            proof.to_vec(),
            instances.to_vec(),
        ));
        for f in 0..=RANDOM_FRAMES {
            let mut rng = ChaCha8Rng::seed_from_u64(seed.wrapping_add(f as u64));
            let mut proof_f = proof.to_vec();
            for i in 0..honest_evals.len() {
                let value = Fq::random(&mut rng);
                proof_f[offset + 32 * i..offset + 32 * (i + 1)]
                    .copy_from_slice(value.to_repr().as_ref());
            }
            if f < RANDOM_FRAMES {
                frames.push((format!("random frame {f}"), proof_f, instances.to_vec()));
            } else {
                assert!(!instances.is_empty(), "{label}: no public input to change");
                let mut changed = instances.to_vec();
                changed[0] = Fq::random(&mut rng);
                frames.push((
                    "random frame + changed public input (new challenges)".to_string(),
                    proof_f,
                    changed,
                ));
            }
        }

        let mut report = ProbeReport {
            frames: 0,
            changed_challenge_frames: 0,
            identities: 0,
            gate_identities: 0,
            selector_buckets: selector_columns.len(),
            lowerings: probes.len(),
        };
        for (kind, proof_f, instances_f) in &frames {
            let events = native_events::<H>(vk, proof_f, instances_f);
            let frame_y = fq(&events[&Y_ID].1);
            if kind.contains("changed") {
                assert_ne!(
                    frame_y, honest_y,
                    "{label}: changed public input must change y"
                );
                report.changed_challenge_frames += 1;
            } else if kind.starts_with("random") {
                assert_ne!(
                    main_evals(&events),
                    honest_evals,
                    "{label}: {kind} must change the evaluations"
                );
            }
            let reference = reference(
                label,
                vk,
                &events,
                nb_committed_instances,
                &selector_columns,
            );
            let calldata =
                generator.encode_calldata(proof_f, instances_f).expect("calldata encoding");
            for (lowering, address) in &probes {
                let output = match evm.try_call_with_gas(*address, calldata.clone(), 5_000_000_000)
                {
                    CallOutcome::Success { output, .. } => output,
                    other => panic!(
                        "{label} {kind}: {lowering:?} quotient probe did not return: {other:?}"
                    ),
                };
                assert_eq!(
                    output.len(),
                    32 * (1 + selector_columns.len()),
                    "{label} {kind}: {lowering:?} probe output length"
                );
                let words: Vec<Fq> = output.chunks(32).map(fq).collect();
                let mut mismatches = Vec::new();
                let members = |b: Option<usize>| {
                    (0..reference.m)
                        .filter(|j| reference.bucket[*j] == b)
                        .map(|j| {
                            format!("{j} ({})", names.get(j).map(String::as_str).unwrap_or("?"))
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                if words[0] != reference.expected_eval {
                    mismatches.push(format!(
                        "expected_eval (QUOTIENT_EVAL_MPTR, fully evaluated identities): probe {} reference {}; folds identities {}",
                        hex(&words[0]),
                        hex(&reference.expected_eval),
                        members(None)
                    ));
                }
                for (s, col) in selector_columns.iter().enumerate() {
                    if words[1 + s] != reference.selector_acc[s] {
                        mismatches.push(format!(
                            "selector bucket {s} (fixed column {col}): probe {} reference {}; folds identities {}",
                            hex(&words[1 + s]),
                            hex(&reference.selector_acc[s]),
                            members(Some(s))
                        ));
                    }
                }
                if !mismatches.is_empty() {
                    let identities = localise(generator, *lowering, &calldata, &reference, &names);
                    panic!(
                        "{label} {kind}: {lowering:?} quotient probe differs from the Rust reference\n  {}\n  identity values of a {lowering:?} trace render that differ from midnight-proofs:\n  {}",
                        mismatches.join("\n  "),
                        if identities.is_empty() {
                            "(none)".to_string()
                        } else {
                            identities.join("\n  ")
                        }
                    );
                }
            }
            report.frames += 1;
            report.identities = reference.m;
            report.gate_identities = reference.gate_identities;
        }
        eprintln!(
            "[quotient-probe] {label}: {} frames ({} with changed challenges) x {} lowerings (Direct, Vm): \
             expected_eval and {} selector buckets equal the Rust reference; m = {} identities \
             ({} gate identities re-evaluated with Expression::evaluate)",
            report.frames,
            report.changed_challenge_frames,
            report.lowerings,
            report.selector_buckets,
            report.identities,
            report.gate_identities
        );
        report
    }
}

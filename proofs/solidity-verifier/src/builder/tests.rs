// SPDX-License-Identifier: CC0-1.0
//! Builder facade tests.
//!
//! These tests cover public-shape validation plus a few lowering helpers that
//! used to live on `SolidityGenerator`.

use super::SolidityGenerator;
use crate::{
    api::GeneratorError,
    lowering::{
        quotient::{NativeGateCandidate, QuotientComputationBlocks},
        quotient_numerator::vm::QuotientProgramBuild,
        VerifierBuildInputs,
    },
};

#[test]
fn instance_column_shape_validation_is_exact() {
    assert!(SolidityGenerator::validate_instance_column_shape(2, 1).is_ok());

    for (total, committed) in [(2, 0), (2, 2), (1, 1), (3, 1)] {
        assert!(
            matches!(
                SolidityGenerator::validate_instance_column_shape(total, committed),
                Err(GeneratorError::UnsupportedInstanceColumnShape { .. })
            ),
            "shape total={total}, committed={committed} should be rejected"
        );
    }
}

#[test]
fn quotient_stack_words_cover_native_callback_scratch() {
    let build = QuotientProgramBuild {
        bytes: Vec::new(),
        consts: Vec::new(),
        max_stack: 3,
        used_ops: Vec::new(),
        used_mem_tokens: Vec::new(),
    };

    assert_eq!(
        VerifierBuildInputs::quotient_stack_words_for_build(&build, 0),
        3
    );
    assert_eq!(
        VerifierBuildInputs::quotient_stack_words_for_build(&build, 2),
        3
    );
    assert_eq!(
        VerifierBuildInputs::quotient_stack_words_for_build(&build, 8),
        8
    );
}

#[test]
fn native_gate_knapsack_prefers_gas_under_byte_budget() {
    let candidates = vec![
        NativeGateCandidate {
            gate_idx: 0,
            vm_bytes: 100,
            native_bytes: 320,
            gas_saved: 100,
        },
        NativeGateCandidate {
            gate_idx: 1,
            vm_bytes: 80,
            native_bytes: 160,
            gas_saved: 60,
        },
        NativeGateCandidate {
            gate_idx: 2,
            vm_bytes: 70,
            native_bytes: 160,
            gas_saved: 55,
        },
    ];

    let selection = VerifierBuildInputs::select_native_gate_candidates(&candidates, 2, 320);
    assert_eq!(selection.gate_indices, vec![1, 2]);
    assert_eq!(selection.gas_saved, 115);
    assert_eq!(selection.native_bytes, 320);
}

#[test]
fn native_gate_default_budget_preserves_old_top_n_byte_envelope() {
    let candidates = vec![
        NativeGateCandidate {
            gate_idx: 0,
            vm_bytes: 100,
            native_bytes: 300,
            gas_saved: 1,
        },
        NativeGateCandidate {
            gate_idx: 1,
            vm_bytes: 80,
            native_bytes: 200,
            gas_saved: 1,
        },
        NativeGateCandidate {
            gate_idx: 2,
            vm_bytes: 70,
            native_bytes: 100,
            gas_saved: 1,
        },
    ];

    assert_eq!(
        VerifierBuildInputs::default_native_gate_byte_budget(&candidates, 2),
        500
    );
}

#[test]
fn quotient_helper_flags_scan_all_computation_block_families() {
    let blocks = QuotientComputationBlocks {
        inline_computations: vec![vec!["let a := q_pow5(x)".to_string()]],
        native_lookup_computation: vec!["let b := q_limb7(x0, x1, x2, x3, x4, x5, x6)".to_string()],
        native_identity_computations: vec![vec![
            "let c := q_limb7_wide(x0, x1, x2, x3, x4, x5, x6)".to_string(),
        ]],
        ..Default::default()
    };

    let flags = blocks.helper_flags();

    assert!(flags.pow5);
    assert!(flags.limb7);
    assert!(flags.wide_limb7);
}

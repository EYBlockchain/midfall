// SPDX-License-Identifier: CC0-1.0
//! Quotient planning and lowering for a concrete verifier build.
//!
//! These methods build compact quotient VM artifacts, native callback choices,
//! selector folds, and execution manifests for the concrete verifying key bound
//! to the generator.

use std::collections::{HashMap, HashSet};

use ff::{Field, PrimeField};
use midnight_curves::Fq;
use midnight_proofs::plonk::Expression;

use crate::{
    api::QuotientIdentitySource,
    lowering::{
        config,
        encoding::{fe_to_u256, ConstraintSystemMeta, Data, Ptr},
        layout::{
            memory::{VerifierMemoryLayout, WORD_BYTES},
            vk_payload::PackedProgramCodec,
        },
        quotient_numerator::{vm::*, Evaluator},
        render::{
            Halo2VerifyingKey, QuotientExternal, QuotientProgram, QuotientSelectorTail,
            QuotientVmMemUsage, QuotientVmOpcodeUsage,
        },
        VerifierBuildInputs,
    },
};

/// Persistent quotient VM state words before optional selector-power storage.
pub(crate) const QUOTIENT_FIXED_STATE_WORDS: usize = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct QuotientStateSlots {
    // Persistent VM state words shared by inline prefixes, bytecode identities,
    // and native callbacks so they advance the same y-batch.
    pub(crate) eval_numer_mptr: usize,
    pub(crate) trace_id_mptr: usize,
    pub(crate) selector_power_mptr: usize,
}

impl QuotientStateSlots {
    /// Place persistent VM state at the start of the quotient state region.
    fn new(state_mptr: usize) -> Self {
        // Layout at `quotient_tmp_mptr`:
        //   [0 .. +2 words)         accumulator and trace-id state
        //   [after state]           optional y^k selector power table
        Self {
            eval_numer_mptr: state_mptr,
            trace_id_mptr: state_mptr + WORD_BYTES,
            selector_power_mptr: state_mptr + 2 * WORD_BYTES,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct NativeGateCandidate {
    pub(crate) gate_idx: usize,
    pub(crate) vm_bytes: usize,
    pub(crate) native_bytes: usize,
    pub(crate) gas_saved: u64,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct NativeGateSelectionState {
    pub(crate) gas_saved: u64,
    pub(crate) native_bytes: usize,
    pub(crate) gate_indices: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct QuotientComputationBlocks {
    pub(crate) inline_computations: Vec<Vec<String>>,
    pub(crate) eval_numer_computations: Vec<Vec<String>>,
    pub(crate) post_vm_computations: Vec<Vec<String>>,
    pub(crate) native_permutation_computation: Vec<String>,
    pub(crate) native_lookup_computation: Vec<String>,
    pub(crate) native_identity_computations: Vec<Vec<String>>,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct QuotientHelperFlags {
    pub(crate) pow5: bool,
    pub(crate) limb7: bool,
    pub(crate) wide_limb7: bool,
}

impl QuotientComputationBlocks {
    /// Scan generated Yul blocks for optional helper calls the template must
    /// include.
    pub(crate) fn helper_flags(&self) -> QuotientHelperFlags {
        QuotientHelperFlags {
            pow5: self.any_line_contains("q_pow5("),
            limb7: self.any_line_contains("q_limb7("),
            wide_limb7: self.any_line_contains("q_limb7_wide("),
        }
    }

    /// Return true if any emitted quotient block references `needle`.
    fn any_line_contains(&self, needle: &str) -> bool {
        self.inline_computations.iter().any(|block| block_contains(block, needle))
            || self.eval_numer_computations.iter().any(|block| block_contains(block, needle))
            || self.post_vm_computations.iter().any(|block| block_contains(block, needle))
            || block_contains(&self.native_permutation_computation, needle)
            || block_contains(&self.native_lookup_computation, needle)
            || self
                .native_identity_computations
                .iter()
                .any(|block| block_contains(block, needle))
    }
}

/// Return true if any generated Yul line in `block` contains `needle`.
fn block_contains(block: &[String], needle: &str) -> bool {
    block.iter().any(|line| line.contains(needle))
}

impl<'params, 'meta> VerifierBuildInputs<'params, 'meta> {
    /// Build the compact quotient VM artifact for a metadata/data snapshot.
    pub(super) fn compact_quotient_program_for(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
    ) -> (QuotientProgramBuild, Vec<usize>) {
        // Build the exact compact program carried by the VK. This helper is
        // also used during static-layout convergence, so its output must be
        // deterministic for a fixed VK base and proof shape.
        let plan = self.quotient_program_plan(meta, data);
        let sorted_simple = plan.sorted_simple.clone();
        let quotient_program_build =
            self.build_quotient_program_items(&plan.items, &plan.selector_fold);
        let _quotient_max_stack = quotient_program_build.max_stack;
        (quotient_program_build, sorted_simple)
    }

    /// Convert a finalized VM build into the template's VK-backed program
    /// model.
    ///
    /// This is the single handoff point between the quotient bytecode compiler,
    /// VK payload reservation, and the generated Yul interpreter. Keeping the
    /// bounds checks here prevents the standalone evaluator and in-verifier VM
    /// paths from drifting.
    pub(super) fn quotient_template_program(
        &self,
        build: QuotientProgramBuild,
        vk: &Halo2VerifyingKey,
        vk_mptr: Ptr,
        memory: &VerifierMemoryLayout,
        selector_fold: &SelectorFoldPlan,
    ) -> (QuotientProgram, usize, QuotientStateSlots) {
        let quotient_program_chunks = PackedProgramCodec::encode_words(&build.bytes);
        let quotient_const_words = vk.quotient_const_words;
        let quotient_program_words = vk.quotient_program_words;
        let quotient_const_offset_words =
            vk.quotient_const_offset_words.expect("VK must carry quotient constants");
        let quotient_program_offset_words =
            vk.quotient_program_offset_words.expect("VK must carry quotient program");
        assert!(
            build.consts.len() <= quotient_const_words,
            "quotient const table exceeded VK payload reservation"
        );
        assert!(
            quotient_program_chunks.len() <= quotient_program_words,
            "quotient program length exceeded VK payload reservation"
        );

        let quotient_stack_mptr = memory.quotient_stack_mptr;
        let const_mptr = (vk_mptr + quotient_const_offset_words).value().as_usize();
        let program_mptr = (vk_mptr + quotient_program_offset_words).value().as_usize();
        let state_slots = QuotientStateSlots::new(memory.quotient_tmp_mptr);
        let len = build.bytes.len();
        let op_usage = Self::quotient_opcode_usage(&build.used_ops);
        let mem_usage = Self::quotient_mem_usage(&build.used_mem_tokens);
        let program = QuotientProgram {
            len,
            op_usage,
            mem_usage,
            const_mptr,
            eval_numer_mptr: state_slots.eval_numer_mptr,
            trace_id_mptr: state_slots.trace_id_mptr,
            selector_power_mptr: state_slots.selector_power_mptr,
            selector_max_power: selector_fold.max_power,
            selector_tail_updates: Self::selector_tail_updates(selector_fold),
            stack_mptr: quotient_stack_mptr,
            program_mptr,
        };

        (program, quotient_stack_mptr, state_slots)
    }

    /// Convert finalized bytecode usage into template switch-arm flags.
    fn quotient_opcode_usage(used_ops: &[u8]) -> QuotientVmOpcodeUsage {
        let has = |op| used_ops.contains(&op);
        QuotientVmOpcodeUsage {
            push_const: has(Q_OP_PUSH_CONST),
            push_mem_literal: has(Q_OP_PUSH_MEM_LITERAL),
            push_mem_token: has(Q_OP_PUSH_MEM_TOKEN),
            push_mem_token_offset: has(Q_OP_PUSH_MEM_TOKEN_OFFSET),
            push_mem_u16: has(Q_OP_PUSH_MEM_U16),
            add: has(Q_OP_ADD),
            mul: has(Q_OP_MUL),
            neg: has(Q_OP_NEG),
            push_const_u8: has(Q_OP_PUSH_CONST_U8),
            fold_main: has(Q_OP_FOLD_MAIN),
            fold_selector: has(Q_OP_FOLD_SELECTOR),
            add_const_u8: has(Q_OP_ADD_CONST_U8),
            mul_const_u8: has(Q_OP_MUL_CONST_U8),
            add_const: has(Q_OP_ADD_CONST),
            mul_const: has(Q_OP_MUL_CONST),
            add_mem_u16: has(Q_OP_ADD_MEM_U16),
            mul_mem_u16: has(Q_OP_MUL_MEM_U16),
            add_mul_mem_mem_const_u8: has(Q_OP_ADD_MUL_MEM_MEM_CONST_U8),
            add_mul_const_u8_mem_u16: has(Q_OP_ADD_MUL_CONST_U8_MEM_U16),
            add_mul_mem_mem: has(Q_OP_ADD_MUL_MEM_MEM),
            run_add_mul_mem_mem_const_u8: has(Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8),
            run_add_mul_const_u8_mem_u16: has(Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16),
            affine_sum: has(Q_OP_AFFINE_SUM),
            native_permutation: has(Q_OP_NATIVE_PERMUTATION),
            native_lookup: has(Q_OP_NATIVE_LOOKUP),
            native_identity: has(Q_OP_NATIVE_IDENTITY),
            lin7: has(Q_OP_LIN7),
            bilin7_row: has(Q_OP_BILIN7_ROW),
            bilin7_pairwise: has(Q_OP_BILIN7_PAIRWISE),
            modarith7: has(Q_OP_MODARITH7),
            pow5: has(Q_OP_POW5),
        }
    }

    /// Convert finalized memory-token usage into template switch-arm flags.
    fn quotient_mem_usage(used_tokens: &[u8]) -> QuotientVmMemUsage {
        let has = |token| used_tokens.contains(&token);
        QuotientVmMemUsage {
            l0: has(Q_MEM_L0),
            l_last: has(Q_MEM_L_LAST),
            l_blind: has(Q_MEM_L_BLIND),
            beta: has(Q_MEM_BETA),
            gamma: has(Q_MEM_GAMMA),
            x: has(Q_MEM_X),
            theta: has(Q_MEM_THETA),
            trash_challenge: has(Q_MEM_TRASH_CHALLENGE),
            instance_eval: has(Q_MEM_INSTANCE_EVAL),
        }
    }

    /// Return stack/scratch words needed by interpreted VM and native
    /// callbacks.
    pub(crate) fn quotient_stack_words_for_build(
        build: &QuotientProgramBuild,
        native_callback_scratch_words: usize,
    ) -> usize {
        // `build.max_stack` only describes the interpreted operand stack. Some
        // native callbacks share `quotient_stack_mptr` as a scratch base, so
        // the registered memory region must cover both possible users.
        build.max_stack.max(native_callback_scratch_words)
    }

    /// Number of persistent VM temp words needed for state plus selector
    /// powers.
    pub(super) fn quotient_state_words(selector_fold: &SelectorFoldPlan) -> usize {
        QUOTIENT_FIXED_STATE_WORDS + Self::selector_power_words(selector_fold)
    }

    /// Number of `y^k` words needed by selector gap/tail folding.
    fn selector_power_words(selector_fold: &SelectorFoldPlan) -> usize {
        if selector_fold.max_power == 0 {
            0
        } else {
            selector_fold.max_power + 1
        }
    }

    /// Render-time selector tail updates, omitting zero tails.
    fn selector_tail_updates(selector_fold: &SelectorFoldPlan) -> Vec<QuotientSelectorTail> {
        selector_fold
            .tail_exponents
            .iter()
            .enumerate()
            .filter_map(|(selector_idx, tail)| {
                (*tail != 0).then_some(QuotientSelectorTail {
                    selector_offset: selector_idx * WORD_BYTES,
                    power_offset: tail * WORD_BYTES,
                })
            })
            .collect()
    }

    /// Build the codegen-time selector gap schedule over the full identity
    /// stream.
    pub(crate) fn selector_fold_plan(
        identities: &[QuotientIdentity],
        selector_count: usize,
    ) -> SelectorFoldPlan {
        let selector_positions = (0..selector_count)
            .map(|selector_idx| {
                identities
                    .iter()
                    .filter_map(|identity| match identity.target {
                        QuotientTarget::Selector(idx) if idx == selector_idx => {
                            Some(identity.meta.global_index)
                        }
                        QuotientTarget::Selector(_) | QuotientTarget::Main => None,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let target_by_global_index = identities
            .iter()
            .map(|identity| (identity.meta.global_index, identity.target))
            .collect::<HashMap<_, _>>();
        let selector_gap_by_global_index = selector_positions
            .iter()
            .flat_map(|positions| {
                positions.iter().enumerate().map(|(pos, &global_index)| {
                    let gap =
                        pos.checked_sub(1).map_or(0, |prev_pos| global_index - positions[prev_pos]);
                    (global_index, gap)
                })
            })
            .collect::<HashMap<_, _>>();

        let gaps_by_identity = (0..identities.len())
            .map(|global_index| {
                match target_by_global_index
                    .get(&global_index)
                    .copied()
                    .expect("quotient identity global indices must be dense")
                {
                    QuotientTarget::Selector(_) => Some(
                        *selector_gap_by_global_index
                            .get(&global_index)
                            .expect("selector identity must be present in selector gaps"),
                    ),
                    QuotientTarget::Main => None,
                }
            })
            .collect::<Vec<_>>();
        let tail_exponents = selector_positions
            .iter()
            .map(|positions| {
                positions.last().map_or(0, |last_index| identities.len() - 1 - last_index)
            })
            .collect::<Vec<_>>();
        let max_power = gaps_by_identity
            .iter()
            .flatten()
            .chain(tail_exponents.iter())
            .copied()
            .max()
            .unwrap_or(0);

        SelectorFoldPlan {
            gaps_by_identity,
            tail_exponents,
            max_power,
        }
    }

    /// Choose inline, VM, and native-callback representation for identities.
    pub(super) fn quotient_program_plan(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
    ) -> QuotientProgramPlan {
        // Preserve the Rust identity order while choosing an execution form for
        // each identity:
        //   * a small gate prefix can stay inline,
        //   * ordinary identities become compact VM bytecode,
        //   * recognized expensive gates plus regular permutation/lookup families
        //     become native callback markers in the same stream.
        let parts = self.quotient_identity_parts(meta, data);
        let all_identities = parts.all_identities();
        let selector_fold = Self::selector_fold_plan(&all_identities, parts.sorted_simple.len());
        let inline_count = parts.gates.len().min(config::DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES);
        let inline_identities = parts.gates[..inline_count].to_vec();
        let remaining_gates = &parts.gates[inline_count..];
        let native_gate_indices = Self::native_gate_indices(remaining_gates);
        let native_permutation = meta.num_permutation_zs > 0;
        let native_lookup = meta.num_lookups > 0;
        let structured_trash_tail = meta.num_trashcans > 0;

        let native_identities = remaining_gates
            .iter()
            .enumerate()
            .filter(|(gate_idx, _)| native_gate_indices.contains(gate_idx))
            .map(|(_, identity)| identity.clone())
            .collect::<Vec<_>>();
        let native_index_by_gate = remaining_gates
            .iter()
            .enumerate()
            .filter(|(gate_idx, _)| native_gate_indices.contains(gate_idx))
            .enumerate()
            .map(|(native_idx, (gate_idx, _))| (gate_idx, native_idx))
            .collect::<HashMap<_, _>>();

        let gate_items = remaining_gates.iter().enumerate().map(|(gate_idx, identity)| {
            native_index_by_gate
                .get(&gate_idx)
                .copied()
                .map(QuotientProgramItem::NativeIdentity)
                .unwrap_or_else(|| QuotientProgramItem::Identity(identity.clone()))
        });
        let permutation_items = if native_permutation {
            vec![QuotientProgramItem::NativePermutation]
        } else {
            parts.permutation.iter().cloned().map(QuotientProgramItem::Identity).collect()
        };
        let lookup_items = if native_lookup {
            vec![QuotientProgramItem::NativeLookup]
        } else {
            parts.lookup.iter().cloned().map(QuotientProgramItem::Identity).collect()
        };
        let trash_items = if structured_trash_tail {
            Vec::new()
        } else {
            parts
                .trash
                .iter()
                .cloned()
                .map(QuotientProgramItem::Identity)
                .collect::<Vec<_>>()
        };
        let items = gate_items
            .chain(permutation_items)
            .chain(lookup_items)
            .chain(trash_items)
            .collect();

        let native_permutation_identities = if native_permutation {
            parts.permutation.clone()
        } else {
            Vec::new()
        };
        let native_lookup_identities = if native_lookup {
            parts.lookup.clone()
        } else {
            Vec::new()
        };
        let structured_tail_identities = if structured_trash_tail {
            parts.trash.clone()
        } else {
            Vec::new()
        };

        let plan = QuotientProgramPlan {
            inline_identities,
            items,
            native_identities,
            native_permutation_identities,
            native_lookup_identities,
            structured_tail_identities,
            sorted_simple: parts.sorted_simple,
            has_native_permutation: native_permutation,
            has_native_lookup: native_lookup,
            selector_fold,
        };
        plan.validate_execution_manifest(&all_identities)
            .expect("quotient execution plan must preserve the identity stream");
        plan
    }

    /// Pick native gate callbacks by estimated gas saved under a byte budget.
    fn native_gate_indices(gates: &[QuotientIdentity]) -> HashSet<usize> {
        let max_count = gates.len().min(config::DEFAULT_QUOTIENT_NATIVE_GATES);
        if max_count == 0 {
            return HashSet::new();
        }

        let candidates = Self::native_gate_candidates(gates);
        let byte_budget = Self::default_native_gate_byte_budget(&candidates, max_count);
        let selection = Self::select_native_gate_candidates(&candidates, max_count, byte_budget);

        selection.gate_indices.into_iter().collect()
    }

    /// Build per-gate native-callback selection metrics.
    fn native_gate_candidates(gates: &[QuotientIdentity]) -> Vec<NativeGateCandidate> {
        gates
            .iter()
            .enumerate()
            .map(|(gate_idx, identity)| {
                let (vm_bytes, vm_gas) = Self::quotient_identity_program_metrics(identity);
                let native_block = Self::native_identity_estimate_block(identity);
                let native_bytes = Self::yul_block_source_bytes(&native_block);
                let native_gas = Self::estimate_native_yul_gas(&native_block);
                NativeGateCandidate {
                    gate_idx,
                    vm_bytes,
                    native_bytes,
                    gas_saved: vm_gas.saturating_sub(native_gas),
                }
            })
            .collect()
    }

    /// Preserve the previous top-N byte envelope as the default native budget.
    pub(crate) fn default_native_gate_byte_budget(
        candidates: &[NativeGateCandidate],
        max_count: usize,
    ) -> usize {
        let mut ranked = candidates
            .iter()
            .map(|candidate| {
                (
                    candidate.vm_bytes,
                    candidate.gate_idx,
                    candidate.native_bytes,
                )
            })
            .collect::<Vec<_>>();
        ranked.sort_by(|(lhs_bytes, lhs_idx, _), (rhs_bytes, rhs_idx, _)| {
            rhs_bytes.cmp(lhs_bytes).then_with(|| lhs_idx.cmp(rhs_idx))
        });
        ranked
            .into_iter()
            .take(max_count)
            .map(|(_, _, native_bytes)| native_bytes)
            .sum()
    }

    /// Solve a small 0/1 knapsack: maximize estimated gas saved under bytes.
    pub(crate) fn select_native_gate_candidates(
        candidates: &[NativeGateCandidate],
        max_count: usize,
        byte_budget: usize,
    ) -> NativeGateSelectionState {
        if max_count == 0 || byte_budget == 0 {
            return NativeGateSelectionState::default();
        }

        // Round byte budgets to EVM-word units to keep the dynamic-programming
        // table small while preserving the byte-budget ordering.
        const BYTE_UNIT: usize = 32;
        let budget_units = byte_budget.div_ceil(BYTE_UNIT);
        let mut dp = vec![vec![None::<NativeGateSelectionState>; budget_units + 1]; max_count + 1];
        dp[0][0] = Some(NativeGateSelectionState::default());

        for candidate in candidates
            .iter()
            .filter(|candidate| candidate.gas_saved > 0 && candidate.native_bytes > 0)
        {
            let cost_units = candidate.native_bytes.div_ceil(BYTE_UNIT).max(1);
            if cost_units > budget_units {
                continue;
            }

            for count in (0..max_count).rev() {
                for used in (0..=budget_units - cost_units).rev() {
                    let Some(state) = dp[count][used].clone() else {
                        continue;
                    };
                    let mut next = state;
                    next.gas_saved += candidate.gas_saved;
                    next.native_bytes += candidate.native_bytes;
                    next.gate_indices.push(candidate.gate_idx);

                    let next_count = count + 1;
                    let next_used = used + cost_units;
                    if Self::native_gate_selection_better(&next, dp[next_count][next_used].as_ref())
                    {
                        dp[next_count][next_used] = Some(next);
                    }
                }
            }
        }

        let mut best = NativeGateSelectionState::default();
        for count_states in dp {
            for state in count_states.into_iter().flatten() {
                if Self::native_gate_selection_better(&state, Some(&best)) {
                    best = state;
                }
            }
        }
        best
    }

    /// Deterministic tie-breaker for native gate knapsack states.
    fn native_gate_selection_better(
        candidate: &NativeGateSelectionState,
        incumbent: Option<&NativeGateSelectionState>,
    ) -> bool {
        let Some(incumbent) = incumbent else {
            return true;
        };
        candidate
            .gas_saved
            .cmp(&incumbent.gas_saved)
            .then_with(|| incumbent.native_bytes.cmp(&candidate.native_bytes))
            .then_with(|| incumbent.gate_indices.len().cmp(&candidate.gate_indices.len()))
            .then_with(|| incumbent.gate_indices.cmp(&candidate.gate_indices))
            == std::cmp::Ordering::Greater
    }

    /// Estimate the generated native callback block for one identity.
    fn native_identity_estimate_block(identity: &QuotientIdentity) -> Vec<String> {
        let state_slots = QuotientStateSlots {
            eval_numer_mptr: 0x2000,
            trace_id_mptr: 0x2020,
            selector_power_mptr: 0x2040,
        };
        let selector_gap = matches!(identity.target, QuotientTarget::Selector(_)).then_some(1);
        Self::direct_quotient_block(
            &identity.lines,
            &identity.var,
            identity.target,
            selector_gap,
            0x1000,
            state_slots,
            false,
        )
    }

    /// Source-byte proxy for the native callback's contribution to runtime
    /// size.
    fn yul_block_source_bytes(block: &[String]) -> usize {
        block.iter().map(|line| line.len() + 1).sum()
    }

    /// Relative gas proxy for a generated native Yul callback.
    fn estimate_native_yul_gas(block: &[String]) -> u64 {
        let raw = block
            .iter()
            .map(|line| {
                let mut gas = 4u64;
                gas += 8 * line.matches("mload(").count() as u64;
                gas += 10 * line.matches("mstore(").count() as u64;
                gas += 38 * line.matches("addmod(").count() as u64;
                gas += 42 * line.matches("mulmod(").count() as u64;
                gas += 18 * line.matches("add(").count() as u64;
                gas += 18 * line.matches("sub(").count() as u64;
                gas += 16 * line.matches("mul(").count() as u64;
                gas
            })
            .sum::<u64>();
        // This is a relative selector score, not an absolute EVM gas model:
        // straight-line native Yul avoids the compact VM's dispatch overhead.
        raw / 2
    }

    /// Estimate compact-VM byte and gas cost of one identity.
    fn quotient_identity_program_metrics(identity: &QuotientIdentity) -> (usize, u64) {
        let mut builder = QuotientProgramBuilder::default();
        let expr = Self::quotient_identity_expr(identity);
        let selector_gap = matches!(identity.target, QuotientTarget::Selector(_)).then_some(0);
        builder.identity_expr(&expr, identity.target, selector_gap);
        let gas = Self::estimate_quotient_vm_gas(&builder.bytes);
        (builder.bytes.len(), gas)
    }

    /// Relative gas proxy for the compact quotient VM interpreter.
    fn estimate_quotient_vm_gas(bytes: &[u8]) -> u64 {
        quotient_bytecode_ops(bytes)
            .map(|(idx, op, len)| match op {
                Q_OP_PUSH_CONST => 54,
                Q_OP_PUSH_MEM_LITERAL => 56,
                Q_OP_PUSH_MEM_TOKEN => 60,
                Q_OP_PUSH_MEM_TOKEN_OFFSET => 66,
                Q_OP_PUSH_MEM_U16 => 48,
                Q_OP_ADD => 38,
                Q_OP_MUL => 42,
                Q_OP_NEG => 24,
                Q_OP_PUSH_CONST_U8 => 42,
                Q_OP_FOLD_MAIN => 70,
                Q_OP_FOLD_SELECTOR => 92,
                Q_OP_ADD_CONST_U8 | Q_OP_ADD_CONST => 46,
                Q_OP_MUL_CONST_U8 | Q_OP_MUL_CONST => 50,
                Q_OP_ADD_MEM_U16 => 48,
                Q_OP_MUL_MEM_U16 => 52,
                Q_OP_ADD_MUL_MEM_MEM_CONST_U8 => 78,
                Q_OP_ADD_MUL_CONST_U8_MEM_U16 => 66,
                Q_OP_ADD_MUL_MEM_MEM => 70,
                Q_OP_RUN_ADD_MUL_MEM_MEM_CONST_U8 => {
                    let count = read_u16(bytes, idx + 1) as u64;
                    32 + 58 * count
                }
                Q_OP_RUN_ADD_MUL_CONST_U8_MEM_U16 => {
                    let count = read_u16(bytes, idx + 1) as u64;
                    32 + 48 * count
                }
                Q_OP_NATIVE_PERMUTATION | Q_OP_NATIVE_LOOKUP => 0,
                Q_OP_NATIVE_IDENTITY => 0,
                Q_OP_LIN7 => 190,
                Q_OP_BILIN7_ROW => 260,
                Q_OP_BILIN7_PAIRWISE => 980,
                Q_OP_MODARITH7 => 90 + 9 * quotient_op_len(bytes, idx) as u64,
                Q_OP_POW5 => 58,
                _ => len as u64 * 12,
            })
            .sum()
    }

    /// Compute the copied-memory frame required by the external evaluator.
    pub(super) fn quotient_external_frame(
        vk_mptr: Ptr,
        vk_len: usize,
        meta: &ConstraintSystemMeta,
        memory: &VerifierMemoryLayout,
        simple_selector_count: usize,
    ) -> QuotientExternal {
        let frame_base = vk_mptr.value().as_usize();
        Self::quotient_external_frame_from_bounds(
            frame_base,
            vk_len,
            memory.reversed_evals_mptr.value().as_usize(),
            meta.num_evals,
            simple_selector_count,
        )
    }

    /// Compute an external quotient frame from already-known range bounds.
    pub(crate) fn quotient_external_frame_from_bounds(
        frame_base: usize,
        vk_len: usize,
        evals_base: usize,
        num_evals: usize,
        simple_selector_count: usize,
    ) -> QuotientExternal {
        let vk_end = frame_base + vk_len;
        let evals_end = evals_base + num_evals * WORD_BYTES;
        let frame_end = vk_end.max(evals_end);
        QuotientExternal {
            frame_base,
            frame_len: frame_end - frame_base,
            output_len: 2 * WORD_BYTES + simple_selector_count * WORD_BYTES,
            magic: QUOTIENT_EXTERNAL_MAGIC,
        }
    }

    /// Split the quotient identity stream into gate/permutation/lookup/trash
    /// parts.
    ///
    /// Upstream reference: `plonk::partially_evaluate_identities` returns gate
    /// identities first, then permutation, lookup, and trash identities, with
    /// simple-selector gates tagged by their fixed-column index. This method
    /// preserves that order and converts selector columns into local bucket
    /// indices used by the generated linearization MSM.
    pub(super) fn quotient_identity_parts(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
    ) -> QuotientIdentityParts {
        // This is the codegen-time split of Midfall's
        // `partially_evaluate_identities` comment: the Rust verifier returns
        // `(Option<selector_column>, evaluation)` for gates first, then
        // permutation, lookup, and trash identities. `Some(selector_column)`
        // means the identity is gated by a simple multiplicative selector and
        // must feed a selector bucket in `compute_linearization_commitment`;
        // `None` means it is fully evaluated and contributes to the negated
        // expected scalar.
        let evaluator = Evaluator::new(self.vk.cs(), meta, data);
        let gate_items = evaluator.gate_computations_tagged();
        let gate_exprs = self
            .vk
            .cs()
            .gates()
            .iter()
            .flat_map(|gate| gate.polynomials().iter())
            .map(|poly| Self::quotient_expr_from_plonk_expr(meta, data, poly))
            .collect::<Vec<_>>();
        assert_eq!(
            gate_items.len(),
            gate_exprs.len(),
            "gate Yul expressions and typed expressions must stay aligned"
        );
        let perm_items = evaluator.permutation_computations();
        let lookup_items = evaluator.lookup_computations();
        let trash_items = evaluator.trashcan_computations();

        let mut sorted_simple: Vec<usize> = meta.simple_selector_cols.iter().copied().collect();
        sorted_simple.sort_unstable();

        let gate_count = gate_items.len();
        let permutation_base = gate_count;
        let lookup_base = permutation_base + perm_items.len();
        let trash_base = lookup_base + lookup_items.len();

        let selector_target = |col| {
            let idx = sorted_simple
                .iter()
                .position(|simple| *simple == col)
                .expect("selector column present");
            QuotientTarget::Selector(idx)
        };
        let gates = gate_items
            .into_iter()
            .zip(gate_exprs)
            .enumerate()
            .map(|(global_index, (item, expr))| {
                let target =
                    item.simple_selector_index.map(selector_target).unwrap_or(QuotientTarget::Main);
                QuotientIdentity {
                    meta: QuotientIdentityMetadata {
                        global_index,
                        source: QuotientIdentitySource::Gate {
                            gate_index: item.gate_index,
                            gate_name: item.gate_name,
                            constraint_index: item.constraint_index,
                            constraint_name: item.constraint_name,
                            polynomial_index: item.polynomial_index,
                        },
                    },
                    lines: item.lines,
                    var: item.var,
                    target,
                    expr,
                }
            })
            .collect::<Vec<_>>();
        let permutation = perm_items
            .into_iter()
            .enumerate()
            .map(|(identity_index, (lines, var))| {
                let expr = Self::quotient_yul_expr(&lines, &var);
                QuotientIdentity {
                    meta: QuotientIdentityMetadata {
                        global_index: permutation_base + identity_index,
                        source: QuotientIdentitySource::Permutation { identity_index },
                    },
                    lines,
                    var,
                    target: QuotientTarget::Main,
                    expr,
                }
            })
            .collect::<Vec<_>>();
        let lookup = lookup_items
            .into_iter()
            .enumerate()
            .map(|(identity_index, (lines, var))| {
                let expr = Self::quotient_yul_expr(&lines, &var);
                let (lookup_index, _) = meta
                    .protocol
                    .lookup_identity_source(identity_index)
                    .expect("lookup identity index covered by protocol lookup chunks");
                let lookup_name = format!("lookup_{lookup_index}");
                QuotientIdentity {
                    meta: QuotientIdentityMetadata {
                        global_index: lookup_base + identity_index,
                        source: QuotientIdentitySource::Lookup {
                            identity_index,
                            lookup_index,
                            lookup_name,
                        },
                    },
                    lines,
                    var,
                    target: QuotientTarget::Main,
                    expr,
                }
            })
            .collect::<Vec<_>>();
        let trash = trash_items
            .into_iter()
            .enumerate()
            .map(|(trash_index, (lines, var))| {
                let expr = Self::quotient_yul_expr(&lines, &var);
                let trash_name = self.trash_manifest_name(trash_index);
                QuotientIdentity {
                    meta: QuotientIdentityMetadata {
                        global_index: trash_base + trash_index,
                        source: QuotientIdentitySource::Trash {
                            trash_index,
                            trash_name,
                        },
                    },
                    lines,
                    var,
                    target: QuotientTarget::Main,
                    expr,
                }
            })
            .collect::<Vec<_>>();

        assert_eq!(
            gates.len(),
            meta.protocol.quotient.gates,
            "gate identity count must match protocol plan"
        );
        assert_eq!(
            permutation.len(),
            meta.protocol.quotient.permutation,
            "permutation identity count must match protocol plan"
        );
        assert_eq!(
            lookup.len(),
            meta.protocol.quotient.lookup,
            "lookup identity count must match protocol plan"
        );
        assert_eq!(
            trash.len(),
            meta.protocol.quotient.trash,
            "trash identity count must match protocol plan"
        );

        QuotientIdentityParts {
            gates,
            permutation,
            lookup,
            trash,
            sorted_simple,
        }
    }

    /// Return the typed quotient expression.
    fn quotient_identity_expr(identity: &QuotientIdentity) -> QuotientExpr {
        identity.expr.clone()
    }

    /// Parse an evaluator-emitted Yul identity into the quotient AST once at
    /// plan-construction time.
    fn quotient_yul_expr(lines: &[String], var: &str) -> QuotientExpr {
        let mut parser = QuotientProgramBuilder::default();
        for line in lines {
            parser.assignment(line);
        }
        parser.parse_expr(var)
    }

    /// Lower a Halo2 expression into the quotient AST using generated data.
    fn quotient_expr_from_plonk_expr(
        meta: &ConstraintSystemMeta,
        data: &Data,
        expression: &Expression<Fq>,
    ) -> QuotientExpr {
        quotient_expr_from_expression(&DataQuotientExpressionEnv { meta, data }, expression)
    }

    /// Emit one direct/native quotient identity block and its y-fold side
    /// effects.
    fn direct_quotient_block(
        lines: &[String],
        var: &str,
        target: QuotientTarget,
        selector_gap: Option<usize>,
        eval_scratch_slot: usize,
        state_slots: QuotientStateSlots,
        trace: bool,
    ) -> Vec<String> {
        let mut block = Vec::with_capacity(lines.len() + 6);
        block.push("{".to_string());
        let lines = Self::specialize_limb7_chains(lines);
        for line in &lines {
            block.push(line.clone());
        }
        block.push(format!("mstore({eval_scratch_slot:#x}, {var})"));
        block.push("}".to_string());
        Self::push_quotient_trace(
            &mut block,
            state_slots,
            format!("mload({eval_scratch_slot:#x})"),
            trace,
        );
        Self::push_structured_fold_advance(&mut block, 1, "q_direct_fold_i", state_slots);
        match target {
            QuotientTarget::Main => {
                Self::push_quotient_eval_numer_add(
                    &mut block,
                    state_slots,
                    format!("mload({eval_scratch_slot:#x})"),
                );
            }
            QuotientTarget::Selector(idx) => {
                let offset = idx * 0x20;
                let gap = selector_gap.expect("selector gap for compact direct quotient block");
                block.push("{".to_string());
                block.push(format!(
                    "let q_selector_ptr := add(SELECTOR_ACC_MPTR, {offset:#x})"
                ));
                block.push("let q_selector_acc := mload(q_selector_ptr)".to_string());
                if gap != 0 {
                    block.push(format!(
                        "q_selector_acc := mulmod(q_selector_acc, mload(add({:#x}, {:#x})), r)",
                        state_slots.selector_power_mptr,
                        gap * WORD_BYTES
                    ));
                }
                block.push(format!(
                    "mstore(q_selector_ptr, addmod(q_selector_acc, mload({eval_scratch_slot:#x}), r))"
                ));
                block.push("}".to_string());
            }
        }
        block
    }

    /// Append trace emission for a quotient identity value.
    fn push_quotient_trace(
        block: &mut Vec<String>,
        state_slots: QuotientStateSlots,
        value: impl AsRef<str>,
        trace: bool,
    ) {
        if !trace {
            return;
        }

        let value = value.as_ref();
        block.push(format!(
            "trace_u256(mload({:#x}), {value})",
            state_slots.trace_id_mptr
        ));
        block.push(format!(
            "mstore({:#x}, add(mload({:#x}), 1))",
            state_slots.trace_id_mptr, state_slots.trace_id_mptr
        ));
    }

    /// Add an identity value into the current numerator accumulator.
    fn push_quotient_eval_numer_add(
        block: &mut Vec<String>,
        state_slots: QuotientStateSlots,
        value: impl AsRef<str>,
    ) {
        let value = value.as_ref();
        block.push(format!(
            "mstore({:#x}, addmod(mload({:#x}), {value}, r))",
            state_slots.eval_numer_mptr, state_slots.eval_numer_mptr
        ));
    }

    /// Advance the global y-fold state by `count` identity positions.
    ///
    /// Compact VM mode advances only the main accumulator here: selector
    /// buckets use codegen-time gap updates at selector identity positions.
    fn push_structured_fold_advance(
        block: &mut Vec<String>,
        count: usize,
        loop_var: &str,
        state_slots: QuotientStateSlots,
    ) {
        let push_one = |block: &mut Vec<String>| {
            block.push(format!(
                "mstore({:#x}, mulmod(mload({:#x}), y, r))",
                state_slots.eval_numer_mptr, state_slots.eval_numer_mptr
            ));
        };

        if count == 1 {
            push_one(block);
            return;
        }

        block.push(format!(
            "for {{ let {loop_var} := 0 }} lt({loop_var}, {count}) {{ {loop_var} := add({loop_var}, 1) }} {{"
        ));
        push_one(block);
        block.push("}".to_string());
    }

    /// Compact runs of adjacent `mstore(dst+i, mload(src+i*stride))` lines.
    ///
    /// Native callbacks often stage contiguous eval tables. This helper emits a
    /// small copy loop when the staged source and destination offsets form a
    /// regular run, otherwise it leaves the original store shape intact.
    fn push_mstore_mload_literal_runs(
        block: &mut Vec<String>,
        dst: &str,
        entries: &[(usize, String)],
        loop_prefix: &str,
    ) {
        let mut idx = 0usize;
        while idx < entries.len() {
            let (dst_base, expr) = &entries[idx];
            let Some(src_base) = yul_mload_literal_expr(expr) else {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            };
            let Some((next_dst, next_expr)) = entries.get(idx + 1) else {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            };
            if *next_dst != *dst_base + 0x20 {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            }
            let Some(next_src) = yul_mload_literal_expr(next_expr) else {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            };
            let Some(src_stride) = next_src.checked_sub(src_base) else {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            };
            if src_stride == 0 {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            }

            let mut count = 2usize;
            while let Some((candidate_dst, candidate_expr)) = entries.get(idx + count) {
                let Some(candidate_src) = yul_mload_literal_expr(candidate_expr) else {
                    break;
                };
                if *candidate_dst != *dst_base + count * 0x20
                    || candidate_src != src_base + count * src_stride
                {
                    break;
                }
                count += 1;
            }

            if count < 3 {
                block.push(format!("mstore(add({dst}, {dst_base:#x}), {expr})"));
                idx += 1;
                continue;
            }

            block.push("{".to_string());
            block.push(format!(
                "for {{ let {loop_prefix}_i := 0 }} lt({loop_prefix}_i, {count}) {{ {loop_prefix}_i := add({loop_prefix}_i, 1) }} {{"
            ));
            block.push(format!(
                "let {loop_prefix}_dst_off := shl(5, {loop_prefix}_i)"
            ));
            if src_stride == 0x20 {
                block.push(format!(
                    "let {loop_prefix}_src_off := {loop_prefix}_dst_off"
                ));
            } else {
                block.push(format!(
                    "let {loop_prefix}_src_off := mul({loop_prefix}_i, {src_stride:#x})"
                ));
            }
            block.push(format!(
                "mstore(add(add({dst}, {dst_base:#x}), {loop_prefix}_dst_off), mload(add({src_base:#x}, {loop_prefix}_src_off)))"
            ));
            block.push("}".to_string());
            block.push("}".to_string());
            idx += count;
        }
    }

    /// Replace recognized seven-limb linear chains with helper calls.
    ///
    /// This operates on legacy/direct Yul text, not on the compact VM AST. The
    /// VM has its own structural limb opcodes; this helper keeps native Yul
    /// callbacks compact for the same foreign-field shapes.
    pub(crate) fn specialize_limb7_chains(lines: &[String]) -> Vec<String> {
        let mut out = Vec::with_capacity(lines.len());
        let mut const_vars = HashMap::new();
        let mut idx = 0usize;

        while idx < lines.len() {
            if let Some((consumed, replacement, updated_consts)) =
                Self::try_limb7_chain(&lines[idx..], &const_vars, &LIMB7_YUL_COEFFS, "q_limb7")
                    .or_else(|| {
                        Self::try_limb7_chain(
                            &lines[idx..],
                            &const_vars,
                            &WIDE_LIMB7_YUL_COEFFS,
                            "q_limb7_wide",
                        )
                    })
            {
                const_vars = updated_consts;
                out.extend(replacement);
                idx += consumed;
                continue;
            }

            Self::record_yul_const_assignment(&lines[idx], &mut const_vars);
            out.push(lines[idx].clone());
            idx += 1;
        }

        out
    }

    /// Try to recognize one helper-compatible seven-limb add/mul chain.
    fn try_limb7_chain(
        lines: &[String],
        const_vars: &HashMap<String, String>,
        coeffs: &[&str; 6],
        helper_name: &str,
    ) -> Option<(usize, Vec<String>, HashMap<String, String>)> {
        let mut idx = 0usize;
        let mut keep = Vec::new();
        let mut args = Vec::with_capacity(7);
        let mut previous_acc: Option<String> = None;
        let mut local_consts = const_vars.clone();

        for (step, coeff) in coeffs.iter().enumerate() {
            let mut skipped = 0usize;
            let (mul_dst, mul_arg) = loop {
                if idx >= lines.len() || skipped > 4 {
                    return None;
                }

                if let Some((dst, arg)) =
                    Self::parse_limb7_mul_assignment(&lines[idx], coeff, &local_consts)
                {
                    break (dst, arg);
                }

                if yul_let_assignment(&lines[idx]).is_some() {
                    Self::record_yul_const_assignment(&lines[idx], &mut local_consts);
                    keep.push(lines[idx].clone());
                    idx += 1;
                    skipped += 1;
                } else {
                    return None;
                }
            };

            let (add_dst, lhs, rhs) = yul_addmod_assignment(lines.get(idx + 1)?)?;
            let addend = if lhs == mul_dst {
                rhs
            } else if rhs == mul_dst {
                lhs
            } else {
                return None;
            };

            if step == 0 {
                args.push(addend);
            } else if Some(addend.as_str()) != previous_acc.as_deref() {
                return None;
            }
            args.push(mul_arg);
            previous_acc = Some(add_dst);
            idx += 2;
        }

        let final_acc = previous_acc?;
        keep.push(format!(
            "let {final_acc} := {helper_name}({})",
            args.join(", ")
        ));
        Some((idx, keep, local_consts))
    }

    /// Parse one `mulmod(coeff, limb, r)` line in a limb7 chain.
    fn parse_limb7_mul_assignment(
        line: &str,
        expected_coeff: &str,
        const_vars: &HashMap<String, String>,
    ) -> Option<(String, String)> {
        let (dst, lhs, rhs) = yul_mulmod_assignment(line)?;
        if Self::yul_coeff_matches(&lhs, expected_coeff, const_vars) {
            Some((dst, rhs))
        } else if Self::yul_coeff_matches(&rhs, expected_coeff, const_vars) {
            Some((dst, lhs))
        } else {
            None
        }
    }

    /// Return whether a literal or constant variable equals `expected_coeff`.
    fn yul_coeff_matches(
        value: &str,
        expected_coeff: &str,
        const_vars: &HashMap<String, String>,
    ) -> bool {
        yul_const_value(value, const_vars).as_deref() == Some(expected_coeff)
    }

    /// Record `let name := const` bindings for later limb-chain matching.
    fn record_yul_const_assignment(line: &str, const_vars: &mut HashMap<String, String>) {
        let Some((dst, rhs)) = yul_let_assignment(line) else {
            return;
        };
        let Some(value) = yul_const_value(&rhs, const_vars) else {
            return;
        };
        const_vars.insert(dst, value);
    }

    /// Trace, advance, and accumulate one main quotient identity value.
    fn push_structured_main_fold(
        block: &mut Vec<String>,
        value: impl AsRef<str>,
        state_slots: QuotientStateSlots,
        trace: bool,
    ) {
        Self::push_quotient_trace(block, state_slots, value.as_ref(), trace);
        Self::push_structured_fold_advance(block, 1, "q_main_fold_i", state_slots);
        Self::push_quotient_eval_numer_add(block, state_slots, value.as_ref());
    }

    /// Scratch table width used by the native permutation callback.
    fn structured_permutation_scratch_words(meta: &ConstraintSystemMeta) -> usize {
        if meta.num_permutation_zs == 0 {
            return 0;
        }

        let num_cols = meta.permutation_columns.len();
        let num_sets = meta.num_permutation_zs;
        // Native permutation code materializes the terms for every permutation
        // set into a contiguous scratch table rooted at the callback scratch
        // pointer. This is separate from VM operand-stack depth even when both
        // regions currently use `quotient_stack_mptr` as their base.
        // permutation values, permutation sigma values, z_cur, z_next,
        // z_last for every non-final set, and one spill slot for the
        // running delta base used by the native permutation callback.
        (2 * num_cols) + (2 * num_sets) + num_sets.saturating_sub(1) + 1
    }

    /// Maximum parallel input width across LogUp lookup chunks.
    fn structured_lookup_max_parallel(&self, meta: &ConstraintSystemMeta) -> usize {
        if meta.num_lookups == 0 {
            return 0;
        }

        self.vk
            .cs()
            .lookups()
            .iter()
            .flat_map(|lookup| {
                let chunked = lookup.chunk_by_degree(self.vk.cs().degree());
                chunked
                    .input_expression_chunks()
                    .iter()
                    .map(|input_chunk| input_chunk.len())
                    .collect::<Vec<_>>()
            })
            .max()
            .unwrap_or(1)
    }

    /// Scratch table width used by the native lookup callback.
    fn structured_lookup_scratch_words(&self, meta: &ConstraintSystemMeta) -> usize {
        // Native lookup stages f+beta values plus prefix and suffix products.
        self.structured_lookup_max_parallel(meta) * 3
    }

    /// Largest scratch table needed by any enabled native VM callback.
    pub(super) fn native_callback_scratch_words(
        &self,
        meta: &ConstraintSystemMeta,
        plan: &QuotientProgramPlan,
    ) -> usize {
        let permutation_words = if plan.has_native_permutation {
            Self::structured_permutation_scratch_words(meta)
        } else {
            0
        };
        let lookup_words = if plan.has_native_lookup {
            self.structured_lookup_scratch_words(meta)
        } else {
            0
        };
        permutation_words.max(lookup_words)
    }

    /// Emit a native structured loop for the full permutation identity block.
    ///
    /// The formula follows the upstream permutation verifier/evaluator:
    /// first-set boundary, last-set booleanity, set-to-set continuity, and
    /// active-row product equality for each chunk.
    fn structured_permutation_loop_block(
        meta: &ConstraintSystemMeta,
        data: &Data,
        evaluator: &Evaluator<'_>,
        scratch_mptr: usize,
        state_slots: QuotientStateSlots,
        trace: bool,
    ) -> Option<Vec<String>> {
        if meta.num_permutation_zs == 0 {
            return None;
        }

        let num_cols = meta.permutation_columns.len();
        let num_sets = meta.num_permutation_zs;
        let chunk_len = meta.permutation_chunk_len;
        let vals_mptr = scratch_mptr;
        let sigmas_mptr = vals_mptr + num_cols * 0x20;
        let z_cur_mptr = sigmas_mptr + num_cols * 0x20;
        let z_next_mptr = z_cur_mptr + num_sets * 0x20;
        let z_last_mptr = z_next_mptr + num_sets * 0x20;
        let delta_base_mptr = z_last_mptr + num_sets.saturating_sub(1) * 0x20;
        let delta_chunk = Fq::DELTA.pow_vartime([chunk_len as u64]);
        let delta_chunk = u256_string(fe_to_u256::<Fq>(&delta_chunk));
        let delta = fr_delta_literal();

        let mut block = Vec::new();
        block.push("{".to_string());
        block.push(format!("let delta := {delta}"));
        block.push(format!("let q_perm_vals := {vals_mptr:#x}"));
        block.push(format!("let q_perm_sigmas := {sigmas_mptr:#x}"));
        block.push(format!("let q_perm_z_cur := {z_cur_mptr:#x}"));
        block.push(format!("let q_perm_z_next := {z_next_mptr:#x}"));
        block.push(format!("let q_perm_z_last := {z_last_mptr:#x}"));
        block.push(format!("let q_perm_delta_base_ptr := {delta_base_mptr:#x}"));
        block.push(format!("let q_perm_num_cols := {num_cols}"));
        block.push(format!("let q_perm_num_sets := {num_sets}"));
        block.push(format!("let q_perm_chunk_len := {chunk_len}"));
        block.push(format!("let q_perm_delta_chunk := {delta_chunk}"));

        let mut value_entries = Vec::with_capacity(num_cols);
        let mut sigma_entries = Vec::with_capacity(num_cols);
        for (idx, column) in meta.permutation_columns.iter().enumerate() {
            let offset = idx * 0x20;
            let value = evaluator.eval_at(column, 0);
            let sigma = data
                .permutation_evals
                .get(column)
                .expect("permutation sigma eval present")
                .to_string();
            value_entries.push((offset, value));
            sigma_entries.push((offset, sigma));
        }
        Self::push_mstore_mload_literal_runs(
            &mut block,
            "q_perm_vals",
            &value_entries,
            "q_perm_val_load",
        );
        Self::push_mstore_mload_literal_runs(
            &mut block,
            "q_perm_sigmas",
            &sigma_entries,
            "q_perm_sigma_load",
        );

        let mut z_cur_entries = Vec::with_capacity(data.permutation_z_evals.len());
        let mut z_next_entries = Vec::with_capacity(data.permutation_z_evals.len());
        let mut z_last_entries = Vec::with_capacity(data.permutation_z_evals.len());
        for (idx, (z_cur, z_next, z_last)) in data.permutation_z_evals.iter().enumerate() {
            let offset = idx * 0x20;
            z_cur_entries.push((offset, z_cur.to_string()));
            z_next_entries.push((offset, z_next.to_string()));
            if let Some(z_last) = z_last {
                z_last_entries.push((offset, z_last.to_string()));
            }
        }
        Self::push_mstore_mload_literal_runs(
            &mut block,
            "q_perm_z_cur",
            &z_cur_entries,
            "q_perm_z_cur_load",
        );
        Self::push_mstore_mload_literal_runs(
            &mut block,
            "q_perm_z_next",
            &z_next_entries,
            "q_perm_z_next_load",
        );
        Self::push_mstore_mload_literal_runs(
            &mut block,
            "q_perm_z_last",
            &z_last_entries,
            "q_perm_z_last_load",
        );

        let fold_eval = |block: &mut Vec<String>| {
            Self::push_quotient_trace(block, state_slots, "q_perm_eval", trace);
            Self::push_structured_fold_advance(block, 1, "q_perm_fold_i", state_slots);
            Self::push_quotient_eval_numer_add(block, state_slots, "q_perm_eval");
        };

        block.push("let q_perm_eval := 0".to_string());

        block.push(
            "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(1, sub(r, mload(q_perm_z_cur)), r), r)"
                .to_string(),
        );
        fold_eval(&mut block);

        let final_z_offset = (num_sets - 1) * 0x20;
        block.push(format!(
            "let q_perm_zn := mload(add(q_perm_z_cur, {final_z_offset:#x}))"
        ));
        block.push(
            "q_perm_eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(q_perm_zn, q_perm_zn, r), sub(r, q_perm_zn), r), r)"
                .to_string(),
        );
        fold_eval(&mut block);

        if num_sets > 1 {
            block.push(format!(
                "for {{ let q_perm_i := 1 }} lt(q_perm_i, {num_sets}) {{ q_perm_i := add(q_perm_i, 1) }} {{"
            ));
            block.push("let q_perm_cur := mload(add(q_perm_z_cur, shl(5, q_perm_i)))".to_string());
            block.push(
                "let q_perm_prev := mload(add(q_perm_z_last, shl(5, sub(q_perm_i, 1))))"
                    .to_string(),
            );
            block.push(
                "q_perm_eval := mulmod(mload(L_0_MPTR), addmod(q_perm_cur, sub(r, q_perm_prev), r), r)"
                    .to_string(),
            );
            fold_eval(&mut block);
            block.push("}".to_string());
        }

        block.push(
            "mstore(q_perm_delta_base_ptr, mulmod(mload(BETA_MPTR), mload(X_MPTR), r))".to_string(),
        );
        block.push(format!(
            "for {{ let q_perm_set := 0 }} lt(q_perm_set, {num_sets}) {{ q_perm_set := add(q_perm_set, 1) }} {{"
        ));
        block.push("let q_perm_start := mul(q_perm_set, q_perm_chunk_len)".to_string());
        block.push("let q_perm_end := add(q_perm_start, q_perm_chunk_len)".to_string());
        block.push(
            "if gt(q_perm_end, q_perm_num_cols) { q_perm_end := q_perm_num_cols }".to_string(),
        );
        block.push("let q_perm_left := mload(add(q_perm_z_next, shl(5, q_perm_set)))".to_string());
        block.push("let q_perm_right := mload(add(q_perm_z_cur, shl(5, q_perm_set)))".to_string());
        block.push("let q_perm_delta_pow := mload(q_perm_delta_base_ptr)".to_string());
        block.push("for { let q_perm_j := q_perm_start } lt(q_perm_j, q_perm_end) { q_perm_j := add(q_perm_j, 1) } {".to_string());
        block.push("let q_perm_off := shl(5, q_perm_j)".to_string());
        block.push("let q_perm_v := mload(add(q_perm_vals, q_perm_off))".to_string());
        block.push("let q_perm_s := mload(add(q_perm_sigmas, q_perm_off))".to_string());
        block.push(
            "q_perm_left := mulmod(q_perm_left, addmod(addmod(q_perm_v, mulmod(mload(BETA_MPTR), q_perm_s, r), r), mload(GAMMA_MPTR), r), r)"
                .to_string(),
        );
        block.push(
            "q_perm_right := mulmod(q_perm_right, addmod(addmod(q_perm_v, q_perm_delta_pow, r), mload(GAMMA_MPTR), r), r)"
                .to_string(),
        );
        block.push("q_perm_delta_pow := mulmod(q_perm_delta_pow, delta, r)".to_string());
        block.push("}".to_string());
        block.push(
            "q_perm_eval := mulmod(addmod(1, sub(r, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r)), r), addmod(q_perm_left, sub(r, q_perm_right), r), r)"
                .to_string(),
        );
        fold_eval(&mut block);
        block.push(
            "mstore(q_perm_delta_base_ptr, mulmod(mload(q_perm_delta_base_ptr), q_perm_delta_chunk, r))".to_string(),
        );
        block.push("}".to_string());

        block.push("}".to_string());
        Some(block)
    }

    #[allow(clippy::too_many_arguments)]
    /// Emit a native structured loop for all LogUp lookup identities.
    ///
    /// This adapts the upstream LogUp helper and accumulator constraints while
    /// staging parallel lookup products in scratch to avoid repeated generated
    /// straight-line Yul.
    fn structured_lookup_loop_block(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
        evaluator: &Evaluator<'_>,
        scratch_mptr: usize,
        state_slots: QuotientStateSlots,
        trace: bool,
    ) -> Option<Vec<String>> {
        if meta.num_lookups == 0 {
            return None;
        }

        let max_parallel = self.structured_lookup_max_parallel(meta);

        let f_plus_beta_mptr = scratch_mptr;
        let prefix_mptr = f_plus_beta_mptr + max_parallel * 0x20;
        let suffix_mptr = prefix_mptr + max_parallel * 0x20;

        let mut block = Vec::new();
        block.push("{".to_string());
        block.push(format!("let q_lookup_f := {f_plus_beta_mptr:#x}"));
        block.push(format!("let q_lookup_prefix := {prefix_mptr:#x}"));
        block.push(format!("let q_lookup_suffix := {suffix_mptr:#x}"));
        block.push("let q_lookup_l0 := mload(L_0_MPTR)".to_string());
        block.push("let q_lookup_llast := mload(L_LAST_MPTR)".to_string());
        block.push("let q_lookup_lblind := mload(L_BLIND_MPTR)".to_string());
        block.push("let q_lookup_lsum := addmod(q_lookup_l0, q_lookup_llast, r)".to_string());
        block.push(
            "let q_lookup_active := addmod(1, sub(r, addmod(q_lookup_llast, q_lookup_lblind, r)), r)"
                .to_string(),
        );
        block.push("let q_lookup_beta := mload(BETA_MPTR)".to_string());
        block.push("let q_lookup_theta := mload(THETA_MPTR)".to_string());

        for (lookup_idx, lookup) in self.vk.cs().lookups().iter().enumerate() {
            let chunked = lookup.chunk_by_degree(self.vk.cs().degree());
            let (m_eval, h_evals, z_eval, z_next_eval) = &data.lookup_evals[lookup_idx];

            block.push("{".to_string());

            // boundary = (l_0 + l_last) * Z_lookup(x)
            block.push("{".to_string());
            block.push(format!(
                "let q_lookup_eval := mulmod(q_lookup_lsum, {}, r)",
                z_eval
            ));
            Self::push_structured_main_fold(&mut block, "q_lookup_eval", state_slots, trace);
            block.push("}".to_string());

            for (input_chunk, h_eval) in
                chunked.input_expression_chunks().iter().zip(h_evals.iter())
            {
                let k = input_chunk.len();
                block.push("{".to_string());

                if k == 0 {
                    block.push("let q_lookup_eval := 0".to_string());
                    Self::push_structured_main_fold(
                        &mut block,
                        "q_lookup_eval",
                        state_slots,
                        trace,
                    );
                    block.push("}".to_string());
                    continue;
                }

                if k == 1 {
                    evaluator.reset_locals();
                    let (mut compressed_lines, compressed_var) = evaluator
                        .compress_expressions_with_challenge_var(&input_chunk[0], "q_lookup_theta");
                    block.append(&mut compressed_lines);
                    block.push(format!(
                        "let q_lookup_eval := addmod(mulmod({}, addmod({compressed_var}, q_lookup_beta, r), r), sub(r, 1), r)",
                        h_eval
                    ));
                    Self::push_structured_main_fold(
                        &mut block,
                        "q_lookup_eval",
                        state_slots,
                        trace,
                    );
                    block.push("}".to_string());
                    continue;
                }

                evaluator.reset_locals();
                if let Some(mut shared_prefix_lines) = evaluator.lookup_shared_prefix_f_plus_beta(
                    input_chunk,
                    "q_lookup_theta",
                    "q_lookup_beta",
                    "q_lookup_f",
                ) {
                    block.append(&mut shared_prefix_lines);
                } else {
                    for (input_idx, parallel_input) in input_chunk.iter().enumerate() {
                        let (mut compressed_lines, compressed_var) = evaluator
                            .compress_expressions_with_challenge_var(
                                parallel_input,
                                "q_lookup_theta",
                            );
                        block.append(&mut compressed_lines);
                        block.push(format!(
                            "mstore(add(q_lookup_f, {:#x}), addmod({compressed_var}, q_lookup_beta, r))",
                            input_idx * 0x20
                        ));
                    }
                }

                block.push("let q_lookup_product := 1".to_string());
                block.push(format!(
                    "for {{ let q_lookup_prod_i := 0 }} lt(q_lookup_prod_i, {k}) {{ q_lookup_prod_i := add(q_lookup_prod_i, 1) }} {{"
                ));
                block.push(
                    "q_lookup_product := mulmod(q_lookup_product, mload(add(q_lookup_f, shl(5, q_lookup_prod_i))), r)"
                        .to_string(),
                );
                block.push("}".to_string());

                block.push("mstore(q_lookup_prefix, 1)".to_string());
                if k > 1 {
                    block.push(format!(
                        "for {{ let q_lookup_pref_i := 1 }} lt(q_lookup_pref_i, {k}) {{ q_lookup_pref_i := add(q_lookup_pref_i, 1) }} {{"
                    ));
                    block.push("let q_lookup_pref_prev := sub(q_lookup_pref_i, 1)".to_string());
                    block.push(
                        "mstore(add(q_lookup_prefix, shl(5, q_lookup_pref_i)), mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_pref_prev))), mload(add(q_lookup_f, shl(5, q_lookup_pref_prev))), r))"
                            .to_string(),
                    );
                    block.push("}".to_string());
                }

                block.push(format!(
                    "mstore(add(q_lookup_suffix, {:#x}), 1)",
                    (k - 1) * 0x20
                ));
                if k > 1 {
                    block.push(format!(
                        "for {{ let q_lookup_suf_i := sub({k}, 1) }} gt(q_lookup_suf_i, 0) {{ q_lookup_suf_i := sub(q_lookup_suf_i, 1) }} {{"
                    ));
                    block.push("let q_lookup_suf_prev := sub(q_lookup_suf_i, 1)".to_string());
                    block.push(
                        "mstore(add(q_lookup_suffix, shl(5, q_lookup_suf_prev)), mulmod(mload(add(q_lookup_suffix, shl(5, q_lookup_suf_i))), mload(add(q_lookup_f, shl(5, q_lookup_suf_i))), r))"
                            .to_string(),
                    );
                    block.push("}".to_string());
                }

                block.push("let q_lookup_sum := 0".to_string());
                block.push(format!(
                    "for {{ let q_lookup_sum_i := 0 }} lt(q_lookup_sum_i, {k}) {{ q_lookup_sum_i := add(q_lookup_sum_i, 1) }} {{"
                ));
                block.push(
                    "q_lookup_sum := addmod(q_lookup_sum, mulmod(mload(add(q_lookup_prefix, shl(5, q_lookup_sum_i))), mload(add(q_lookup_suffix, shl(5, q_lookup_sum_i))), r), r)"
                        .to_string(),
                );
                block.push("}".to_string());
                block.push(format!(
                    "let q_lookup_eval := addmod(mulmod({}, q_lookup_product, r), sub(r, q_lookup_sum), r)",
                    h_eval
                ));
                Self::push_structured_main_fold(&mut block, "q_lookup_eval", state_slots, trace);
                block.push("}".to_string());
            }

            // accumulator =
            // active * ((Z_next - Z - selector * sum(h)) * (table + beta) + m)
            block.push("{".to_string());
            let sum_h_expr = if h_evals.is_empty() {
                "0".to_string()
            } else {
                let sum_h = "q_lookup_sum_h";
                block.push(format!("let {sum_h} := {}", h_evals[0]));
                for h_eval in &h_evals[1..] {
                    block.push(format!("{sum_h} := addmod({sum_h}, {}, r)", h_eval));
                }
                sum_h.to_string()
            };

            evaluator.reset_locals();
            let (mut selector_lines, selector_var) =
                evaluator.evaluate_expression(chunked.selector_expression());
            block.append(&mut selector_lines);
            let (mut table_lines, table_var) = evaluator.compress_expressions_with_challenge_var(
                chunked.table_expressions(),
                "q_lookup_theta",
            );
            block.append(&mut table_lines);
            block.push(format!(
                "let q_lookup_s_sum_h := mulmod({selector_var}, {sum_h_expr}, r)"
            ));
            block.push(format!(
                "let q_lookup_diff := addmod({}, sub(r, addmod({}, q_lookup_s_sum_h, r)), r)",
                z_next_eval, z_eval
            ));
            block.push(format!(
                "let q_lookup_t_beta := addmod({table_var}, q_lookup_beta, r)"
            ));
            block.push(format!(
                "let q_lookup_core := addmod(mulmod(q_lookup_diff, q_lookup_t_beta, r), {}, r)",
                m_eval
            ));
            block
                .push("let q_lookup_eval := mulmod(q_lookup_active, q_lookup_core, r)".to_string());
            Self::push_structured_main_fold(&mut block, "q_lookup_eval", state_slots, trace);
            block.push("}".to_string());

            block.push("}".to_string());
        }

        block.push("}".to_string());
        Some(block)
    }

    /// Emit a native structured loop for the trash identity suffix.
    ///
    /// Trash constraints compress their expressions with `trash_challenge` and
    /// subtract `(1 - selector) * trash_eval`, matching the Rust trash
    /// verifier.
    fn structured_trash_loop_block(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
        evaluator: &Evaluator<'_>,
        state_slots: QuotientStateSlots,
        trace: bool,
    ) -> Option<Vec<String>> {
        if meta.num_trashcans == 0 {
            return None;
        }

        let mut block = Vec::new();
        block.push("{".to_string());
        block.push("let q_trash_tau := mload(TRASH_CHALLENGE_MPTR)".to_string());

        for (idx, argument) in self.vk.cs().trashcans().iter().enumerate() {
            block.push("{".to_string());
            evaluator.reset_locals();
            let (mut compressed_lines, compressed_var) = evaluator
                .compress_expressions_with_challenge_var(
                    argument.constraint_expressions(),
                    "q_trash_tau",
                );
            block.append(&mut compressed_lines);
            let (mut selector_lines, selector_var) =
                evaluator.evaluate_expression(argument.selector());
            block.append(&mut selector_lines);
            block.push(format!(
                "let q_trash_one_minus_selector := addmod(1, sub(r, {selector_var}), r)"
            ));
            block.push(format!(
                "let q_trash_scaled := mulmod(q_trash_one_minus_selector, {}, r)",
                data.trashcan_evals[idx]
            ));
            block.push(format!(
                "let q_trash_eval := addmod({compressed_var}, sub(r, q_trash_scaled), r)"
            ));
            Self::push_structured_main_fold(&mut block, "q_trash_eval", state_slots, trace);
            block.push("}".to_string());
        }

        block.push("}".to_string());
        Some(block)
    }

    /// Emit all template blocks for the compact quotient VM representation.
    ///
    /// The main verifier and standalone quotient evaluator both call this
    /// helper, so inline prefixes, native callbacks, structured tails, scratch
    /// slots, and trace behavior stay coupled to the same execution plan.
    pub(super) fn compact_quotient_computation_blocks(
        &self,
        meta: &ConstraintSystemMeta,
        data: &Data,
        quotient_plan: &QuotientProgramPlan,
        quotient_stack_mptr: usize,
        quotient_state_slots: QuotientStateSlots,
        trace: bool,
    ) -> QuotientComputationBlocks {
        let eval_scratch_slot = quotient_stack_mptr;
        let evaluator = Evaluator::new(self.vk.cs(), meta, data).with_pow5_helper(true);
        QuotientComputationBlocks {
            inline_computations: quotient_plan
                .inline_identities
                .iter()
                .map(|identity| {
                    Self::direct_quotient_block(
                        &identity.lines,
                        &identity.var,
                        identity.target,
                        quotient_plan.selector_fold.gap_for(identity),
                        eval_scratch_slot,
                        quotient_state_slots,
                        trace,
                    )
                })
                .collect(),
            eval_numer_computations: Vec::new(),
            post_vm_computations: (meta.num_trashcans > 0)
                .then(|| {
                    self.structured_trash_loop_block(
                        meta,
                        data,
                        &evaluator,
                        quotient_state_slots,
                        trace,
                    )
                })
                .flatten()
                .into_iter()
                .collect(),
            native_permutation_computation: quotient_plan
                .has_native_permutation
                .then(|| {
                    Self::structured_permutation_loop_block(
                        meta,
                        data,
                        &evaluator,
                        quotient_stack_mptr,
                        quotient_state_slots,
                        trace,
                    )
                })
                .flatten()
                .unwrap_or_default(),
            native_lookup_computation: quotient_plan
                .has_native_lookup
                .then(|| {
                    self.structured_lookup_loop_block(
                        meta,
                        data,
                        &evaluator,
                        quotient_stack_mptr,
                        quotient_state_slots,
                        trace,
                    )
                })
                .flatten()
                .unwrap_or_default(),
            native_identity_computations: quotient_plan
                .native_identities
                .iter()
                .map(|identity| {
                    Self::direct_quotient_block(
                        &identity.lines,
                        &identity.var,
                        identity.target,
                        quotient_plan.selector_fold.gap_for(identity),
                        eval_scratch_slot,
                        quotient_state_slots,
                        trace,
                    )
                })
                .collect(),
        }
    }

    /// Lower a logical quotient item stream into compact VM bytecode.
    pub(super) fn build_quotient_program_items(
        &self,
        items: &[QuotientProgramItem],
        selector_fold: &SelectorFoldPlan,
    ) -> QuotientProgramBuild {
        let mut builder = QuotientProgramBuilder::default();
        // Lower the logical plan into bytecode in one pass. Repeated
        // subexpressions are emitted directly; native callbacks remain opaque
        // markers because their arithmetic is emitted as separate Yul kernels
        // in the template.
        for item in items {
            match item {
                QuotientProgramItem::Identity(identity) => {
                    let expr = Self::quotient_identity_expr(identity);
                    builder.identity_expr(&expr, identity.target, selector_fold.gap_for(identity));
                }
                QuotientProgramItem::NativePermutation => builder.native_permutation(),
                QuotientProgramItem::NativeLookup => builder.native_lookup(),
                QuotientProgramItem::NativeIdentity(native_idx) => {
                    builder.native_identity(*native_idx);
                }
            }
        }

        builder.finish()
    }
}
